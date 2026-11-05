-- Prove2me | solution 1 for FoundationsRL.TabularRL.ucbvi_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T09:45:02.975595+00:00
-- url     : https://prove2.me/submissions/c5e4deb5-38e6-473e-88f2-a276fdba1380

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI_v2
import Definitions.Def_FoundationsRL_TabularRL_IsUCBVI
import Definitions.Def_FoundationsRL_TabularRL_regret

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

universe u

namespace UCBVIFR

open FoundationsRL.RLBasics FoundationsRL.TabularRL

/-- Hoeffding's lemma for a finite distribution (from Mathlib's measure-theoretic version). -/
lemma hoeffding_fin {S : Type*} [Fintype S] (p : S → ℝ) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∑ y, p y = 1) (g : S → ℝ) (a b : ℝ) (hg : ∀ y, g y ∈ Set.Icc a b) (t : ℝ) :
    ∑ y, p y * Real.exp (t * (g y - ∑ z, p z * g z)) ≤ Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  classical
  let _ : MeasurableSpace S := ⊤
  have hsum : ∑ y, ENNReal.ofReal (p y) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp0 y), hp1, ENNReal.ofReal_one]
  set q : PMF S := PMF.ofFintype (fun y => ENNReal.ofReal (p y)) hsum with hq
  set μ : MeasureTheory.Measure S := q.toMeasure with hμ
  have hint : ∀ f : S → ℝ, ∫ y, f y ∂μ = ∑ y, p y * f y := by
    intro f
    rw [hμ, PMF.integral_eq_sum]
    apply Finset.sum_congr rfl
    intro y _
    simp [hq, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hp0 y), smul_eq_mul]
  have hm : AEMeasurable g μ := (Measurable.of_discrete).aemeasurable
  have hb : ∀ᵐ y ∂μ, g y ∈ Set.Icc a b := MeasureTheory.ae_of_all μ hg
  have H := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hb
  have h1 := H.mgf_le t
  simp only [ProbabilityTheory.mgf, hint] at h1
  refine le_trans h1 (le_of_eq ?_)
  congr 1
  push_cast
  rw [Real.norm_eq_abs, div_pow, sq_abs]
  ring

/-! ## Part 1. Within-episode path frame on `Fin H → X` (single-coordinate updates). -/

section Frame

variable {X : Type*} [Fintype X] [DecidableEq X] {H : ℕ}

def Agree1 (t : ℕ) (x x' : Fin H → X) : Prop := ∀ j : Fin H, j.val < t → x j = x' j

def Adapted1 {β : Type*} (t : ℕ) (f : (Fin H → X) → β) : Prop :=
  ∀ x x', Agree1 t x x' → f x = f x'

lemma Agree1.mono {t t' : ℕ} (hle : t ≤ t') {x x' : Fin H → X} (h : Agree1 t' x x') :
    Agree1 t x x' := fun j hj => h j (lt_of_lt_of_le hj hle)

lemma agree1_upd (x : Fin H → X) (j : Fin H) (y : X) :
    Agree1 j.val x (Function.update x j y) := by
  intro j' hj'
  have hne : j' ≠ j := fun e => by subst e; exact lt_irrefl _ hj'
  rw [Function.update_of_ne hne]

lemma sum_upd1 (F : (Fin H → X) → ℝ) (j : Fin H) :
    ∑ x, ∑ y, F (Function.update x j y) = (Fintype.card X : ℝ) * ∑ x, F x := by
  have h1 : ∑ p : (Fin H → X) × X, F (Function.update p.1 j p.2) =
      ∑ p : (Fin H → X) × X, F p.1 :=
    Fintype.sum_equiv (Function.Involutive.toPerm
      (fun p : (Fin H → X) × X => (Function.update p.1 j p.2, p.1 j)) (by
        rintro ⟨x, y⟩
        simp)) _ _ (fun p => rfl)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h1
  rw [h1]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- Partial path weight: true kernel factors before time `t`, uniform factors after. -/
noncomputable def ppt1 (q : Fin H → (Fin H → X) → X → ℝ) (t : ℕ) (x : Fin H → X) : ℝ :=
  ∏ j : Fin H, if j.val < t then q j x (x j) else (Fintype.card X : ℝ)⁻¹

lemma ppt1_succ [Nonempty X] (q : Fin H → (Fin H → X) → X → ℝ) (j0 : Fin H) (x : Fin H → X) :
    ppt1 q (j0.val + 1) x = (Fintype.card X : ℝ) * (ppt1 q j0.val x * q j0 x (x j0)) := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold ppt1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0)]
  have hrest : ∏ j ∈ Finset.univ.erase j0,
      (if j.val < j0.val + 1 then q j x (x j) else (Fintype.card X : ℝ)⁻¹) =
      ∏ j ∈ Finset.univ.erase j0,
      (if j.val < j0.val then q j x (x j) else (Fintype.card X : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hne : j.val ≠ j0.val := fun e => Finset.ne_of_mem_erase hj (Fin.ext e)
    have hiff : j.val < j0.val + 1 ↔ j.val < j0.val := by omega
    simp only [hiff]
  rw [hrest]
  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, lt_irrefl, if_true, if_false]
  field_simp

lemma ppt1_adapted (q : Fin H → (Fin H → X) → X → ℝ) (hqad : ∀ j, Adapted1 j.val (q j))
    (t : ℕ) : Adapted1 t (ppt1 q t) := by
  intro x x' hag
  unfold ppt1
  apply Finset.prod_congr rfl
  intro j _
  split_ifs with hlt
  · rw [hqad j x x' (hag.mono hlt.le), hag j hlt]
  · rfl

lemma ppt1_step_eq [Nonempty X] (q : Fin H → (Fin H → X) → X → ℝ)
    (hqad : ∀ j, Adapted1 j.val (q j)) (j0 : Fin H) (Z : (Fin H → X) → ℝ) :
    ∑ x, ppt1 q (j0.val + 1) x * Z x =
      ∑ x, ppt1 q j0.val x * ∑ y, q j0 x y * Z (Function.update x j0 y) := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have key : ∀ x y, ppt1 q (j0.val + 1) (Function.update x j0 y) * Z (Function.update x j0 y) =
      (Fintype.card X : ℝ) * (ppt1 q j0.val x * (q j0 x y * Z (Function.update x j0 y))) := by
    intro x y
    rw [ppt1_succ q j0 (Function.update x j0 y)]
    have a1 := ppt1_adapted q hqad j0.val x (Function.update x j0 y) (agree1_upd x j0 y)
    have a2 := hqad j0 x (Function.update x j0 y) (agree1_upd x j0 y)
    rw [← a1, ← a2, Function.update_self]
    ring
  have hsum := sum_upd1 (fun x => ppt1 q (j0.val + 1) x * Z x) j0
  simp only [key] at hsum
  have e : ∑ x, ∑ y, (Fintype.card X : ℝ) *
      (ppt1 q j0.val x * (q j0 x y * Z (Function.update x j0 y))) =
      (Fintype.card X : ℝ) * ∑ x, ppt1 q j0.val x * ∑ y, q j0 x y * Z (Function.update x j0 y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [e] at hsum
  exact (mul_left_cancel₀ hc.ne' hsum).symm

lemma ppt1_chain [Nonempty X] (q : Fin H → (Fin H → X) → X → ℝ)
    (hqad : ∀ j, Adapted1 j.val (q j)) (hq1 : ∀ j x, ∑ y, q j x y = 1)
    (t0 : ℕ) (Z : (Fin H → X) → ℝ) (hZ : Adapted1 t0 Z) :
    ∀ t, t0 ≤ t → t ≤ H → ∑ x, ppt1 q t x * Z x = ∑ x, ppt1 q t0 x * Z x := by
  intro t
  induction t with
  | zero =>
    intro h0 _
    have e : t0 = 0 := by omega
    subst e
    rfl
  | succ t ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with e | hlt
    · rw [e]
    · obtain ⟨jt, hjt⟩ : ∃ jt : Fin H, jt.val = t := ⟨⟨t, by omega⟩, rfl⟩
      have st := ppt1_step_eq q hqad jt Z
      rw [hjt] at st
      rw [st, ← ih (by omega) (by omega)]
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      have hy : ∀ y, Z (Function.update x jt y) = Z x := fun y =>
        (hZ x _ ((agree1_upd x jt y).mono (by rw [hjt]; omega))).symm
      simp only [hy, ← Finset.sum_mul, hq1, one_mul]

lemma ppt1_full (q : Fin H → (Fin H → X) → X → ℝ) (x : Fin H → X) :
    ppt1 q H x = ∏ j, q j x (x j) := by
  unfold ppt1
  apply Finset.prod_congr rfl
  intro j _
  simp only [j.isLt, if_true]

lemma sum_ppt1_zero [Nonempty X] (q : Fin H → (Fin H → X) → X → ℝ) :
    ∑ x : Fin H → X, ppt1 q 0 x = 1 := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold ppt1
  simp only [Nat.not_lt_zero, if_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_const, nsmul_eq_mul, Fintype.card_fun]
  push_cast
  rw [inv_pow]
  exact mul_inv_cancel₀ (pow_ne_zero _ hc)

lemma prod_sum_one [Nonempty X] (q : Fin H → (Fin H → X) → X → ℝ)
    (hqad : ∀ j, Adapted1 j.val (q j)) (hq1 : ∀ j x, ∑ y, q j x y = 1) :
    ∑ x : Fin H → X, ∏ j, q j x (x j) = 1 := by
  have := ppt1_chain q hqad hq1 0 (fun _ => 1) (fun _ _ _ => rfl) H (Nat.zero_le _) le_rfl
  simp only [mul_one, ppt1_full] at this
  rw [this, sum_ppt1_zero]

/-- Markov property of the product kernel at coordinate `j0`. -/
theorem markov1 [Nonempty X] (q : Fin H → (Fin H → X) → X → ℝ)
    (hqad : ∀ j, Adapted1 j.val (q j)) (hq1 : ∀ j x, ∑ y, q j x y = 1) (j0 : Fin H)
    (G : (Fin H → X) → ℝ) (hG : Adapted1 (j0.val + 1) G) :
    ∑ x, (∏ j, q j x (x j)) * G x =
      ∑ x, (∏ j, q j x (x j)) * ∑ y, q j0 x y * G (Function.update x j0 y) := by
  have hG' : Adapted1 j0.val (fun x => ∑ y, q j0 x y * G (Function.update x j0 y)) := by
    intro x x' hag
    apply Finset.sum_congr rfl
    intro y _
    rw [hqad j0 x x' hag]
    congr 1
    apply hG
    intro j hj
    by_cases e : j = j0
    · subst e
      simp only [Function.update_self]
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact hag j (by have : j.val ≠ j0.val := fun h => e (Fin.ext h); omega)
  have hj0 : j0.val + 1 ≤ H := j0.isLt
  have e1 : ∀ Z : (Fin H → X) → ℝ, ∑ x, (∏ j, q j x (x j)) * Z x = ∑ x, ppt1 q H x * Z x :=
    fun Z => by simp only [ppt1_full]
  rw [e1, e1, ppt1_chain q hqad hq1 _ G hG H hj0 le_rfl,
    ppt1_chain q hqad hq1 _ _ hG' H (by omega) le_rfl]
  exact ppt1_step_eq q hqad j0 G

end Frame

/-! ## Part 2. Trajectories: normalisation, initial marginal and the Markov property. -/

section Traj

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma nonempty_of_M (M : EpisodicMDP S A H) : Nonempty S := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have := M.d1_sum_one
  simp at this

lemma actionAt_fin (τ : Trajectory S A H) (j : Fin H) : actionAt τ j.val = (τ.2 j).1 := by
  simp [actionAt, j.isLt]

lemma nextStateAt_fin (τ : Trajectory S A H) (j : Fin H) : nextStateAt τ j.val = (τ.2 j).2 := by
  simp [nextStateAt, j.isLt]

lemma stateAt_succ (τ : Trajectory S A H) (h : ℕ) : stateAt τ (h + 1) = nextStateAt τ h := rfl

/-- The layer-`j` kernel of a trajectory started at `s0`. -/
noncomputable def qk (M : EpisodicMDP S A H) (π : Policy S A H) (s0 : S) (j : Fin H)
    (x : Fin H → A × S) (y : A × S) : ℝ :=
  π j.val (stateAt ((s0, x) : Trajectory S A H) j.val) y.1 *
    M.P j.val (stateAt ((s0, x) : Trajectory S A H) j.val) y.1 y.2

lemma stateAt_adapted (s0 : S) (j : ℕ) :
    Adapted1 j (fun x : Fin H → A × S => stateAt ((s0, x) : Trajectory S A H) j) := by
  intro x x' hag
  cases j with
  | zero => rfl
  | succ k =>
    show nextStateAt ((s0, x) : Trajectory S A H) k = nextStateAt ((s0, x') : Trajectory S A H) k
    unfold nextStateAt
    split_ifs with hk
    · dsimp only
      rw [hag ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · rfl

lemma qk_adapted (M : EpisodicMDP S A H) (π : Policy S A H) (s0 : S) (j : Fin H) :
    Adapted1 j.val (qk M π s0 j) := by
  intro x x' hag
  funext y
  unfold qk
  have hs : stateAt ((s0, x) : Trajectory S A H) j.val = stateAt ((s0, x') : Trajectory S A H) j.val :=
    stateAt_adapted s0 j.val x x' hag
  rw [hs]

lemma qk_sum (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) (s0 : S)
    (j : Fin H) (x : Fin H → A × S) : ∑ y, qk M π s0 j x y = 1 := by
  unfold qk
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, M.P_sum_one, mul_one]
  exact (hπ j.val j.isLt _).2

lemma trajProb_eq (M : EpisodicMDP S A H) (π : Policy S A H) (s0 : S) (x : Fin H → A × S) :
    trajProb M π ((s0, x) : Trajectory S A H) = M.d1 s0 * ∏ j, qk M π s0 j x (x j) := by
  unfold trajProb qk
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [actionAt_fin, nextStateAt_fin]

lemma trajProb_nonneg (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π)
    (τ : Trajectory S A H) : 0 ≤ trajProb M π τ := by
  unfold trajProb
  apply mul_nonneg (M.d1_nonneg _)
  apply Finset.prod_nonneg
  intro j _
  exact mul_nonneg ((hπ j.val j.isLt _).1 _) (M.P_nonneg _ _ _ _)

lemma prod_qk_sum (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) (s0 : S) :
    ∑ x : Fin H → A × S, ∏ j, qk M π s0 j x (x j) = 1 := by
  have := nonempty_of_M M
  exact prod_sum_one (qk M π s0) (qk_adapted M π s0) (qk_sum M π hπ s0)

theorem sum_trajProb (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    ∑ τ : Trajectory S A H, trajProb M π τ = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [trajProb_eq, ← Finset.mul_sum, prod_qk_sum M π hπ, mul_one]
  exact M.d1_sum_one

theorem traj_init (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) (g : S → ℝ) :
    ∑ τ : Trajectory S A H, trajProb M π τ * g τ.1 = ∑ s, M.d1 s * g s := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s0 _
  simp only [trajProb_eq]
  rw [← Finset.sum_mul, ← Finset.mul_sum, prod_qk_sum M π hπ s0, mul_one]

/-- Markov property at layer `j0`: the action and next state are drawn from `π` and `P`. -/
theorem traj_markov (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) (j0 : Fin H)
    (φ : S → A → S → ℝ) :
    ∑ τ : Trajectory S A H, trajProb M π τ *
        φ (stateAt τ j0.val) (actionAt τ j0.val) (nextStateAt τ j0.val) =
      ∑ τ : Trajectory S A H, trajProb M π τ *
        ∑ a, π j0.val (stateAt τ j0.val) a *
          ∑ s', M.P j0.val (stateAt τ j0.val) a s' * φ (stateAt τ j0.val) a s' := by
  have := nonempty_of_M M
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s0 _
  simp only [trajProb_eq, mul_assoc, ← Finset.mul_sum]
  congr 1
  have hG : Adapted1 (j0.val + 1) (fun x : Fin H → A × S =>
      φ (stateAt ((s0, x) : Trajectory S A H) j0.val) (x j0).1 (x j0).2) := by
    intro x x' hag
    dsimp only
    have hs : stateAt ((s0, x) : Trajectory S A H) j0.val =
        stateAt ((s0, x') : Trajectory S A H) j0.val :=
      stateAt_adapted s0 j0.val x x' (hag.mono (Nat.le_succ _))
    rw [hs, hag j0 (Nat.lt_succ_self _)]
  have mk := markov1 (qk M π s0) (qk_adapted M π s0) (qk_sum M π hπ s0) j0 _ hG
  simp only [actionAt_fin, nextStateAt_fin]
  rw [mk]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  have hs : ∀ y, stateAt ((s0, Function.update x j0 y) : Trajectory S A H) j0.val =
      stateAt ((s0, x) : Trajectory S A H) j0.val :=
    fun y => (stateAt_adapted s0 j0.val x _ (agree1_upd x j0 y)).symm
  simp only [hs, Function.update_self, qk, Fintype.sum_prod_type, mul_assoc, Finset.mul_sum]

end Traj

/-! ## Part 3. Episode-level frame: snoc decomposition and the supermartingale bound. -/

section Episodes

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma ofFn_snoc' {n : ℕ} (h : Fin n → Trajectory S A H) (τ : Trajectory S A H) :
    List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ) = List.ofFn h ++ [τ] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma take_ofFn_snoc {n : ℕ} (h : Fin n → Trajectory S A H) (τ : Trajectory S A H) (i : ℕ)
    (hi : i ≤ n) :
    (List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ)).take i = (List.ofFn h).take i := by
  rw [ofFn_snoc', List.take_append_of_le_length (by simp; omega)]

lemma historyProb_snoc (M : EpisodicMDP S A H) (learner : Learner S A H) {n : ℕ}
    (h : Fin n → Trajectory S A H) (τ : Trajectory S A H) :
    historyProb M learner (Fin.snoc (α := fun _ => Trajectory S A H) h τ) =
      historyProb M learner h * trajProb M (learner (List.ofFn h)) τ := by
  unfold historyProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.snoc_castSucc, Fin.val_castSucc, take_ofFn_snoc h τ i.val (le_of_lt i.isLt)]
  · rw [Fin.snoc_last, Fin.val_last, take_ofFn_snoc h τ n le_rfl,
      List.take_of_length_le (by simp)]

lemma sum_snoc {n : ℕ} (F : (Fin (n + 1) → Trajectory S A H) → ℝ) :
    ∑ g, F g = ∑ h : Fin n → Trajectory S A H, ∑ τ : Trajectory S A H,
      F (Fin.snoc (α := fun _ => Trajectory S A H) h τ) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Trajectory S A H))
    (fun p => F (Fin.snoc (α := fun _ => Trajectory S A H) p.2 p.1)) F (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma historyProb_nonneg (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) {n : ℕ} (h : Fin n → Trajectory S A H) :
    0 ≤ historyProb M learner h := by
  unfold historyProb
  exact Finset.prod_nonneg (fun t _ => trajProb_nonneg M _ (hL _) _)

theorem hist_total (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) :
    ∀ n, ∑ h : Fin n → Trajectory S A H, historyProb M learner h = 1 := by
  intro n
  induction n with
  | zero => simp [historyProb]
  | succ n ih =>
    rw [sum_snoc]
    simp only [historyProb_snoc, ← Finset.mul_sum, sum_trajProb M _ (hL _), mul_one]
    exact ih

/-- Supermartingale bound over episodes. -/
theorem hist_super (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (Ψ : List (Trajectory S A H) → ℝ)
    (hstep : ∀ l, ∑ τ, trajProb M (learner l) τ * Ψ (l ++ [τ]) ≤ Ψ l) :
    ∀ n, ∑ h : Fin n → Trajectory S A H, historyProb M learner h * Ψ (List.ofFn h) ≤ Ψ [] := by
  intro n
  induction n with
  | zero => simp [historyProb]
  | succ n ih =>
    rw [sum_snoc]
    calc ∑ h : Fin n → Trajectory S A H, ∑ τ : Trajectory S A H,
          historyProb M learner (Fin.snoc (α := fun _ => Trajectory S A H) h τ) *
            Ψ (List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ))
        = ∑ h : Fin n → Trajectory S A H, historyProb M learner h *
            ∑ τ, trajProb M (learner (List.ofFn h)) τ * Ψ (List.ofFn h ++ [τ]) := by
          apply Finset.sum_congr rfl
          intro h _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ _
          rw [historyProb_snoc, ofFn_snoc']
          ring
      _ ≤ ∑ h : Fin n → Trajectory S A H, historyProb M learner h * Ψ (List.ofFn h) := by
          apply Finset.sum_le_sum
          intro h _
          exact mul_le_mul_of_nonneg_left (hstep _) (historyProb_nonneg M learner hL h)
      _ ≤ Ψ [] := ih

lemma probEvent_nonneg (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (E : (Fin T → Trajectory S A H) → Prop) :
    0 ≤ probEvent M learner T E := by
  unfold probEvent
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact historyProb_nonneg M learner hL h
  · exact le_rfl

/-- Markov's inequality for a nonnegative list functional dominated on the event. -/
lemma probEvent_le_markov (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (E : (Fin T → Trajectory S A H) → Prop)
    (Ψ : List (Trajectory S A H) → ℝ) (hΨ : ∀ l, 0 ≤ Ψ l) (c : ℝ) (hc : 0 < c)
    (hE : ∀ h, E h → c ≤ Ψ (List.ofFn h))
    (hstep : ∀ l, ∑ τ, trajProb M (learner l) τ * Ψ (l ++ [τ]) ≤ Ψ l) :
    probEvent M learner T E ≤ Ψ [] / c := by
  rw [le_div_iff₀ hc]
  unfold probEvent
  rw [Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum (fun h _ => ?_)) (hist_super M learner hL Ψ hstep T)
  split_ifs with hh
  · exact mul_le_mul_of_nonneg_left (hE h hh) (historyProb_nonneg M learner hL h)
  · rw [zero_mul]
    exact mul_nonneg (historyProb_nonneg M learner hL h) (hΨ _)

lemma probEvent_compl (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (E : (Fin T → Trajectory S A H) → Prop) :
    probEvent M learner T E = 1 - probEvent M learner T (fun h => ¬ E h) := by
  have htot := hist_total M learner hL T
  unfold probEvent
  rw [← htot, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : E h <;> simp [hh]

lemma probEvent_mono (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (E F : (Fin T → Trajectory S A H) → Prop)
    (hEF : ∀ h, E h → F h) : probEvent M learner T E ≤ probEvent M learner T F := by
  unfold probEvent
  apply Finset.sum_le_sum
  intro h _
  by_cases he : E h
  · simp [he, hEF h he]
  · simp only [he, if_false]
    split_ifs
    · exact historyProb_nonneg M learner hL h
    · exact le_rfl

/-- Union bound over a finite index set. -/
lemma probEvent_exists_le {ι : Type*} (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (s : Finset ι)
    (B : ι → (Fin T → Trajectory S A H) → Prop) :
    probEvent M learner T (fun h => ∃ i ∈ s, B i h) ≤ ∑ i ∈ s, probEvent M learner T (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [probEvent]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine le_trans ?_ (add_le_add le_rfl ih)
    unfold probEvent
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro h _
    have h0 := historyProb_nonneg M learner hL h
    by_cases h1 : B i h
    · have : ∃ j ∈ insert i s, B j h := ⟨i, Finset.mem_insert_self _ _, h1⟩
      simp only [this, h1, if_true]
      split_ifs <;> linarith
    · by_cases h2 : ∃ j ∈ s, B j h
      · have : ∃ j ∈ insert i s, B j h := by
          obtain ⟨j, hj, hb⟩ := h2
          exact ⟨j, Finset.mem_insert_of_mem hj, hb⟩
        simp only [this, h1, h2, if_true, if_false]
        linarith
      · have : ¬ ∃ j ∈ insert i s, B j h := by
          rintro ⟨j, hj, hb⟩
          rcases Finset.mem_insert.mp hj with e | hj'
          · exact h1 (e ▸ hb)
          · exact h2 ⟨j, hj', hb⟩
        simp only [this, h1, h2, if_false]
        linarith

end Episodes

/-! ## Part 4. Value functions: recursion, bounds, and the easy half of Bellman optimality. -/

section Values

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma V_lt (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (hh : h < H) (s : S) :
    V M π h s = ∑ a, π h s a * Q M π h s a := by
  obtain ⟨k, hk⟩ : ∃ k, H - h = k + 1 := ⟨H - h - 1, by omega⟩
  have hk' : H - (h + 1) = k := by omega
  have hl : H - 1 - k = h := by omega
  unfold V Q
  rw [hk, valueAux]
  simp only [hl, if_pos hh, V, hk']

lemma V_ge (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (hh : H ≤ h) (s : S) :
    V M π h s = 0 := by
  unfold V
  rw [show H - h = 0 by omega]
  simp only [valueAux]

lemma detPolicy_isPolicy (πdet : ℕ → S → A) : IsPolicy H (detPolicy (H := H) πdet) := by
  intro h _ s
  refine ⟨fun a => ?_, ?_⟩
  · unfold detPolicy
    split_ifs <;> norm_num
  · unfold detPolicy
    simp

lemma V_bounds (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1) :
    ∀ k h, H - h = k → ∀ s, 0 ≤ V M π h s ∧ V M π h s ≤ k := by
  intro k
  induction k with
  | zero =>
    intro h hk s
    have e : V M π h s = 0 := V_ge M π h (by omega) s
    simp [e]
  | succ k ih =>
    intro h hk s
    have hh : h < H := by omega
    have ih' := ih (h + 1) (by omega)
    rw [V_lt M π h hh s]
    have hQ : ∀ a, 0 ≤ Q M π h s a ∧ Q M π h s a ≤ k + 1 := by
      intro a
      unfold Q
      rw [if_pos hh]
      have h1 : 0 ≤ ∑ s', M.P h s a s' * V M π (h + 1) s' :=
        Finset.sum_nonneg (fun s' _ => mul_nonneg (M.P_nonneg _ _ _ _) (ih' s').1)
      have h2 : ∑ s', M.P h s a s' * V M π (h + 1) s' ≤ k := by
        calc _ ≤ ∑ s', M.P h s a s' * (k : ℝ) :=
              Finset.sum_le_sum (fun s' _ =>
                mul_le_mul_of_nonneg_left (ih' s').2 (M.P_nonneg _ _ _ _))
          _ = k := by rw [← Finset.sum_mul, M.P_sum_one, one_mul]
      have hr := hR h hh s a
      constructor <;> linarith [hr.1, hr.2]
    have hp := hπ h hh s
    constructor
    · exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp.1 a) (hQ a).1)
    · calc ∑ a, π h s a * Q M π h s a ≤ ∑ a, π h s a * ((k : ℝ) + 1) :=
            Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hQ a).2 (hp.1 a))
        _ = ((k + 1 : ℕ) : ℝ) := by
            rw [← Finset.sum_mul, hp.2, one_mul]
            push_cast
            ring

lemma V_nonneg (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1) (h : ℕ) (s : S) :
    0 ≤ V M π h s :=
  (V_bounds M π hπ hR (H - h) h rfl s).1

lemma Q_bounds (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1) (h : ℕ) (s : S) (a : A) :
    0 ≤ Q M π h s a ∧ Q M π h s a ≤ H + 1 := by
  unfold Q
  split_ifs with hh
  · have hv := fun s' => V_bounds M π hπ hR (H - (h + 1)) (h + 1) rfl s'
    have h1 : 0 ≤ ∑ s', M.P h s a s' * V M π (h + 1) s' :=
      Finset.sum_nonneg (fun s' _ => mul_nonneg (M.P_nonneg _ _ _ _) (hv s').1)
    have h2 : ∑ s', M.P h s a s' * V M π (h + 1) s' ≤ H := by
      calc _ ≤ ∑ s', M.P h s a s' * (H : ℝ) :=
            Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left
              (le_trans (hv s').2 (by exact_mod_cast Nat.sub_le _ _)) (M.P_nonneg _ _ _ _))
        _ = H := by rw [← Finset.sum_mul, M.P_sum_one, one_mul]
    have hr := hR h hh s a
    constructor <;> linarith [hr.1, hr.2]
  · constructor <;> positivity

local instance validPolicy_nonempty : Nonempty {π : Policy S A H // IsPolicy H π} :=
  ⟨⟨detPolicy (fun _ _ => Classical.arbitrary A), detPolicy_isPolicy _⟩⟩

lemma bdd_Q (M : EpisodicMDP S A H)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1) (h : ℕ) (s : S) (a : A) :
    BddAbove (Set.range fun π : {π : Policy S A H // IsPolicy H π} => Q M π.1 h s a) :=
  ⟨H + 1, by rintro _ ⟨π, rfl⟩; exact (Q_bounds M π.1 π.2 hR h s a).2⟩

lemma Q_le_Qstar (M : EpisodicMDP S A H)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1) (π : Policy S A H)
    (hπ : IsPolicy H π) (h : ℕ) (s : S) (a : A) : Q M π h s a ≤ Qstar M h s a :=
  le_ciSup (f := fun π : {π : Policy S A H // IsPolicy H π} => Q M π.1 h s a)
    (bdd_Q M hR h s a) ⟨π, hπ⟩

lemma Qstar_le_Vstar (M : EpisodicMDP S A H) (h : ℕ) (s : S) (a : A) :
    Qstar M h s a ≤ Vstar M h s :=
  le_ciSup (Set.finite_range _).bddAbove a

lemma iSup_eq_of_argmax {f : A → ℝ} {a : A} (ha : IsArgmax f a) : (⨆ a', f a') = f a :=
  le_antisymm (ciSup_le ha) (le_ciSup (Set.finite_range _).bddAbove a)

lemma Vstar_ge (M : EpisodicMDP S A H) (h : ℕ) (hh : H ≤ h) (s : S) : Vstar M h s = 0 := by
  unfold Vstar Qstar
  simp only [Q, if_neg (not_lt.mpr hh), ciSup_const]

lemma V_le_Vstar (M : EpisodicMDP S A H)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1) (π : Policy S A H)
    (hπ : IsPolicy H π) (h : ℕ) (s : S) : V M π h s ≤ Vstar M h s := by
  by_cases hh : h < H
  · rw [V_lt M π h hh s]
    have hp := hπ h hh s
    calc ∑ a, π h s a * Q M π h s a ≤ ∑ a, π h s a * Vstar M h s :=
          Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
            (le_trans (Q_le_Qstar M hR π hπ h s a) (Qstar_le_Vstar M h s a)) (hp.1 a))
      _ = Vstar M h s := by rw [← Finset.sum_mul, hp.2, one_mul]
  · rw [V_ge M π h (not_lt.mp hh) s, Vstar_ge M h (not_lt.mp hh) s]

/-- The easy half of the Bellman optimality equation. -/
lemma Qstar_le (M : EpisodicMDP S A H)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1) (h : ℕ) (hh : h < H) (s : S)
    (a : A) : Qstar M h s a ≤ M.R h s a + ∑ s', M.P h s a s' * Vstar M (h + 1) s' := by
  unfold Qstar
  apply ciSup_le
  intro π
  unfold Q
  rw [if_pos hh]
  apply add_le_add le_rfl
  exact Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left
    (V_le_Vstar M hR π.1 π.2 (h + 1) s') (M.P_nonneg _ _ _ _))

lemma Qstar_nonneg (M : EpisodicMDP S A H)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1) (h : ℕ) (s : S) (a : A) :
    0 ≤ Qstar M h s a := by
  obtain ⟨π⟩ := (validPolicy_nonempty : Nonempty {π : Policy S A H // IsPolicy H π})
  exact le_trans (Q_bounds M π.1 π.2 hR h s a).1 (Q_le_Qstar M hR π.1 π.2 h s a)

end Values

/-! ## Part 5. Running sums along the history, exponential supermartingales, concentration. -/

section Conc

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

/-- Running sum `∑_i g (prefix_i) (entry_i)` of a list, started after the prefix `pre`. -/
noncomputable def lsumAux (g : List (Trajectory S A H) → Trajectory S A H → ℝ) :
    List (Trajectory S A H) → List (Trajectory S A H) → ℝ
  | _, [] => 0
  | pre, τ :: rest => g pre τ + lsumAux g (pre ++ [τ]) rest

noncomputable def lsum (g : List (Trajectory S A H) → Trajectory S A H → ℝ)
    (l : List (Trajectory S A H)) : ℝ := lsumAux g [] l

lemma lsumAux_append (g : List (Trajectory S A H) → Trajectory S A H → ℝ) :
    ∀ (l1 l2 pre : List (Trajectory S A H)),
    lsumAux g pre (l1 ++ l2) = lsumAux g pre l1 + lsumAux g (pre ++ l1) l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 pre; simp [lsumAux]
  | cons σ rest ih =>
    intro l2 pre
    simp only [List.cons_append, lsumAux]
    rw [ih]
    simp only [List.append_assoc, List.singleton_append]
    ring

lemma lsum_nil (g : List (Trajectory S A H) → Trajectory S A H → ℝ) : lsum g [] = 0 := rfl

lemma lsum_snoc (g : List (Trajectory S A H) → Trajectory S A H → ℝ)
    (l : List (Trajectory S A H)) (τ : Trajectory S A H) :
    lsum g (l ++ [τ]) = lsum g l + g l τ := by
  simp [lsum, lsumAux_append, lsumAux]

lemma lsum_append (g : List (Trajectory S A H) → Trajectory S A H → ℝ)
    (l1 l2 : List (Trajectory S A H)) :
    lsum g (l1 ++ l2) = lsum g l1 + lsumAux g l1 l2 := by
  simp [lsum, lsumAux_append]

lemma lsumAux_zero (g : List (Trajectory S A H) → Trajectory S A H → ℝ)
    (P : List (Trajectory S A H) → Prop) (hP : ∀ l τ, P l → P (l ++ [τ]))
    (hg : ∀ l τ, P l → g l τ = 0) :
    ∀ (rest pre : List (Trajectory S A H)), P pre → lsumAux g pre rest = 0 := by
  intro rest
  induction rest with
  | nil => intro pre _; rfl
  | cons σ rest ih =>
    intro pre hpre
    simp only [lsumAux, hg pre σ hpre, ih (pre ++ [σ]) (hP _ _ hpre), add_zero]

lemma lsum_lin (g w : List (Trajectory S A H) → Trajectory S A H → ℝ) (c d : ℝ)
    (l : List (Trajectory S A H)) :
    lsum (fun l' τ => c * g l' τ + d * w l' τ) l = c * lsum g l + d * lsum w l := by
  induction l using List.reverseRecOn with
  | nil => simp [lsum_nil]
  | append_singleton l τ ih =>
    rw [lsum_snoc, lsum_snoc, lsum_snoc, ih]
    ring

/-- Exponential supermartingale + Markov: if every one-episode exponential moment is `≤ 1`,
the running exponent exceeds `c` with probability at most `exp (-c)`. -/
theorem prob_lsum (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (E : (Fin T → Trajectory S A H) → Prop)
    (G : List (Trajectory S A H) → Trajectory S A H → ℝ)
    (hG : ∀ l, ∑ τ, trajProb M (learner l) τ * Real.exp (G l τ) ≤ 1) (c : ℝ)
    (hE : ∀ h, E h → c ≤ lsum G (List.ofFn h)) :
    probEvent M learner T E ≤ Real.exp (-c) := by
  have key := probEvent_le_markov M learner hL T E (fun l => Real.exp (lsum G l))
    (fun l => (Real.exp_pos _).le) (Real.exp c) (Real.exp_pos c)
    (fun h hh => Real.exp_le_exp.mpr (hE h hh)) (by
      intro l
      calc ∑ τ, trajProb M (learner l) τ * Real.exp (lsum G (l ++ [τ]))
          = Real.exp (lsum G l) * ∑ τ, trajProb M (learner l) τ * Real.exp (G l τ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro τ _
            rw [lsum_snoc, Real.exp_add]
            ring
        _ ≤ Real.exp (lsum G l) * 1 :=
            mul_le_mul_of_nonneg_left (hG l) (Real.exp_pos _).le
        _ = Real.exp (lsum G l) := mul_one _)
  simp only [lsum_nil, Real.exp_zero] at key
  rwa [Real.exp_neg, ← one_div]

lemma countSA_snoc (l : List (Trajectory S A H)) (τ : Trajectory S A H) (h : ℕ) (s : S)
    (a : A) : countSA (l ++ [τ]) h s a =
      countSA l h s a + if stateAt τ h = s ∧ actionAt τ h = a then 1 else 0 := by
  unfold countSA
  rw [List.filter_append, List.length_append]
  by_cases hv : stateAt τ h = s ∧ actionAt τ h = a
  · simp [hv]
  · simp only [hv, if_false]
    simp [List.filter_cons, hv]

lemma countSAS_snoc (l : List (Trajectory S A H)) (τ : Trajectory S A H) (h : ℕ) (s : S)
    (a : A) (y : S) : countSAS (l ++ [τ]) h s a y =
      countSAS l h s a y +
        if stateAt τ h = s ∧ actionAt τ h = a ∧ nextStateAt τ h = y then 1 else 0 := by
  unfold countSAS
  rw [List.filter_append, List.length_append]
  by_cases hv : stateAt τ h = s ∧ actionAt τ h = a ∧ nextStateAt τ h = y
  · simp [hv]
  · simp only [hv, if_false]
    simp [List.filter_cons, hv]

/-- Indicator that episode `τ` visits `(s,a)` at layer `h0` while fewer than `m` earlier visits. -/
noncomputable def vind (h0 : ℕ) (s : S) (a : A) (m : ℕ) (l : List (Trajectory S A H))
    (τ : Trajectory S A H) : ℝ :=
  if stateAt τ h0 = s ∧ actionAt τ h0 = a ∧ countSA l h0 s a < m then 1 else 0

noncomputable def vdev (h0 : ℕ) (s : S) (a : A) (m : ℕ) (f : S → ℝ) (c : ℝ)
    (l : List (Trajectory S A H)) (τ : Trajectory S A H) : ℝ :=
  vind h0 s a m l τ * (f (nextStateAt τ h0) - c)

lemma lsum_vind (h0 : ℕ) (s : S) (a : A) (m : ℕ) (l : List (Trajectory S A H)) :
    lsum (vind h0 s a m) l = ((min (countSA l h0 s a) m : ℕ) : ℝ) := by
  induction l using List.reverseRecOn with
  | nil => simp [lsum_nil, countSA]
  | append_singleton l τ ih =>
    rw [lsum_snoc, ih, countSA_snoc]
    unfold vind
    by_cases hv : stateAt τ h0 = s ∧ actionAt τ h0 = a
    · by_cases hc : countSA l h0 s a < m
      · rw [if_pos ⟨hv.1, hv.2, hc⟩, if_pos hv,
          show min (countSA l h0 s a + 1) m = min (countSA l h0 s a) m + 1 by omega]
        push_cast
        ring
      · rw [if_neg (fun h => hc h.2.2), if_pos hv,
          show min (countSA l h0 s a + 1) m = min (countSA l h0 s a) m by omega]
        simp
    · rw [if_neg (fun h => hv ⟨h.1, h.2.1⟩), if_neg hv]
      simp

lemma lsum_vdev (h0 : ℕ) (s : S) (a : A) (m : ℕ) (f : S → ℝ) (c : ℝ)
    (l : List (Trajectory S A H)) (hl : countSA l h0 s a ≤ m) :
    lsum (vdev h0 s a m f c) l =
      ∑ y, (countSAS l h0 s a y : ℝ) * f y - (countSA l h0 s a : ℝ) * c := by
  induction l using List.reverseRecOn with
  | nil => simp [lsum_nil, countSA, countSAS]
  | append_singleton l τ ih =>
    rw [countSA_snoc] at hl
    rw [lsum_snoc, ih (by split_ifs at hl <;> omega), countSA_snoc]
    simp only [countSAS_snoc]
    unfold vdev vind
    by_cases hv : stateAt τ h0 = s ∧ actionAt τ h0 = a
    · have hc : countSA l h0 s a < m := by rw [if_pos hv] at hl; omega
      rw [if_pos ⟨hv.1, hv.2, hc⟩, if_pos hv]
      simp only [hv.1, hv.2, true_and]
      push_cast
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    · rw [if_neg (fun h => hv ⟨h.1, h.2.1⟩), if_neg hv]
      have hz : ∀ y, ¬ (stateAt τ h0 = s ∧ actionAt τ h0 = a ∧ nextStateAt τ h0 = y) :=
        fun y h => hv ⟨h.1, h.2.1⟩
      simp only [hz, if_false]
      simp

/-- One-episode exponential moment of the `n`-th visit deviation. -/
lemma vstep (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) (h0 : Fin H)
    (s : S) (a : A) (m : ℕ) (f : S → ℝ) (hf : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1) (lam : ℝ)
    (l : List (Trajectory S A H)) :
    ∑ τ, trajProb M π τ * Real.exp (lam * vdev h0.val s a m f (∑ y, M.P h0.val s a y * f y) l τ
      + (-(lam ^ 2 / 8)) * vind h0.val s a m l τ) ≤ 1 := by
  set c := ∑ y, M.P h0.val s a y * f y with hcdef
  by_cases hc : countSA l h0.val s a < m
  · let φ : S → A → S → ℝ := fun x b y =>
      if x = s ∧ b = a then Real.exp (lam * (f y - c) - lam ^ 2 / 8) else 1
    have e : ∀ τ : Trajectory S A H, Real.exp (lam * vdev h0.val s a m f c l τ
        + (-(lam ^ 2 / 8)) * vind h0.val s a m l τ) =
        φ (stateAt τ h0.val) (actionAt τ h0.val) (nextStateAt τ h0.val) := by
      intro τ
      simp only [vdev, vind, φ]
      by_cases hv : stateAt τ h0.val = s ∧ actionAt τ h0.val = a
      · rw [if_pos ⟨hv.1, hv.2, hc⟩, if_pos hv]
        congr 1
        ring
      · rw [if_neg (fun h => hv ⟨h.1, h.2.1⟩), if_neg hv]
        simp
    simp only [e]
    rw [traj_markov M π hπ h0 φ]
    have inner : ∀ x b, ∑ y, M.P h0.val x b y * φ x b y ≤ 1 := by
      intro x b
      by_cases hxb : x = s ∧ b = a
      · obtain ⟨rfl, rfl⟩ := hxb
        simp only [φ, and_self, if_true]
        have hh := hoeffding_fin (M.P h0.val x b) (M.P_nonneg _ _ _) (M.P_sum_one _ _ _) f 0 1
          hf lam
        calc ∑ y, M.P h0.val x b y * Real.exp (lam * (f y - c) - lam ^ 2 / 8)
            = (∑ y, M.P h0.val x b y * Real.exp (lam * (f y - c))) *
                Real.exp (-(lam ^ 2 / 8)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro y _
              rw [sub_eq_add_neg, Real.exp_add]
              ring
          _ ≤ Real.exp (lam ^ 2 * (1 - 0) ^ 2 / 8) * Real.exp (-(lam ^ 2 / 8)) :=
              mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; norm_num
      · simp only [φ, if_neg hxb, mul_one]
        exact (M.P_sum_one _ _ _).le
    calc ∑ τ, trajProb M π τ * ∑ b, π h0.val (stateAt τ h0.val) b *
          ∑ y, M.P h0.val (stateAt τ h0.val) b y * φ (stateAt τ h0.val) b y
        ≤ ∑ τ, trajProb M π τ * 1 := by
          apply Finset.sum_le_sum
          intro τ _
          apply mul_le_mul_of_nonneg_left _ (trajProb_nonneg M π hπ τ)
          have hp := hπ h0.val h0.isLt (stateAt τ h0.val)
          calc ∑ b, π h0.val (stateAt τ h0.val) b *
                ∑ y, M.P h0.val (stateAt τ h0.val) b y * φ (stateAt τ h0.val) b y
              ≤ ∑ b, π h0.val (stateAt τ h0.val) b * 1 :=
                Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (inner _ b) (hp.1 b))
            _ = 1 := by rw [← Finset.sum_mul, hp.2, one_mul]
      _ = 1 := by simp only [mul_one]; exact sum_trajProb M π hπ
  · have e : ∀ τ : Trajectory S A H, lam * vdev h0.val s a m f c l τ
        + (-(lam ^ 2 / 8)) * vind h0.val s a m l τ = 0 := by
      intro τ
      simp [vdev, vind, hc]
    simp only [e, Real.exp_zero, mul_one]
    exact (sum_trajProb M π hπ).le

/-- Value of the running deviation once the visit count has reached `m + 1`. -/
lemma lsum_vdev_trunc (h0 : ℕ) (s : S) (a : A) (m : ℕ) (f : S → ℝ) (c : ℝ)
    (L : List (Trajectory S A H)) (t : ℕ) (ht : countSA (L.take t) h0 s a = m + 1) :
    lsum (vdev h0 s a (m + 1) f c) L =
      ((m : ℝ) + 1) * (estExp (L.take t) h0 s a f - c) := by
  have hsplit := List.take_append_drop t L
  have hz : lsumAux (vdev h0 s a (m + 1) f c) (L.take t) (L.drop t) = 0 :=
    lsumAux_zero _ (fun l' => m + 1 ≤ countSA l' h0 s a)
      (fun l' τ hl' => by rw [countSA_snoc]; omega)
      (fun l' τ hl' => by
        unfold vdev vind
        rw [if_neg (fun h => by omega)]
        ring) _ _ (by rw [ht])
  conv_lhs => rw [← hsplit]
  rw [lsum_append, hz, add_zero, lsum_vdev h0 s a (m + 1) f c _ (by rw [ht])]
  have hest : estExp (L.take t) h0 s a f =
      (∑ y, (countSAS (L.take t) h0 s a y : ℝ) * f y) / ((m : ℝ) + 1) := by
    simp [estExp, ht]
  rw [hest, ht]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- `n`-th visit Hoeffding bound: for a fixed `f ∈ [0,1]`, layer `h0`, pair `(s,a)` and count
`m + 1`, the empirical mean after the `(m+1)`-th visit deviates by more than
`√(ℓ/(2(m+1)))` with probability at most `2 e^{-ℓ}`. -/
theorem conc_event (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (h0 : Fin H) (s : S) (a : A) (m : ℕ)
    (f : S → ℝ) (hf : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    probEvent M learner T (fun hT => ∃ t : ℕ,
      countSA ((List.ofFn hT).take t) h0.val s a = m + 1 ∧
      Real.sqrt (ℓ / (2 * ((m : ℝ) + 1))) <
        |estExp ((List.ofFn hT).take t) h0.val s a f - ∑ y, M.P h0.val s a y * f y|) ≤
      2 * Real.exp (-ℓ) := by
  set c := ∑ y, M.P h0.val s a y * f y with hcdef
  set ε := Real.sqrt (ℓ / (2 * ((m : ℝ) + 1))) with hεdef
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hε2 : ε ^ 2 = ℓ / (2 * ((m : ℝ) + 1)) := Real.sq_sqrt (by positivity)
  have hℓe : 2 * ((m : ℝ) + 1) * ε ^ 2 = ℓ := by rw [hε2]; field_simp
  -- one-sided bound for a sign `σ`
  have side : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      probEvent M learner T (fun hT => ∃ t : ℕ,
        countSA ((List.ofFn hT).take t) h0.val s a = m + 1 ∧
        ε < σ * (estExp ((List.ofFn hT).take t) h0.val s a f - c)) ≤ Real.exp (-ℓ) := by
    intro σ hσ
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    apply prob_lsum M learner hL T _
      (fun l τ => (4 * σ * ε) * vdev h0.val s a (m + 1) f c l τ
        + (-((4 * σ * ε) ^ 2 / 8)) * vind h0.val s a (m + 1) l τ)
      (fun l => vstep M (learner l) (hL l) h0 s a (m + 1) f hf (4 * σ * ε) l) ℓ
    rintro hT ⟨t, ht, hdev⟩
    rw [lsum_lin, lsum_vdev_trunc h0.val s a m f c _ t ht, lsum_vind]
    have hW : ((min (countSA (List.ofFn hT) h0.val s a) (m + 1) : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast min_le_right _ _
    set D := estExp ((List.ofFn hT).take t) h0.val s a f - c
    have h1 : ((m : ℝ) + 1) * ε ≤ ((m : ℝ) + 1) * (σ * D) :=
      mul_le_mul_of_nonneg_left hdev.le hm1.le
    have h2 : 4 * ε * (((m : ℝ) + 1) * ε) ≤ 4 * ε * (((m : ℝ) + 1) * (σ * D)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (4 * σ * ε) ^ 2 / 8 *
        ((min (countSA (List.ofFn hT) h0.val s a) (m + 1) : ℕ) : ℝ) ≤
        (4 * σ * ε) ^ 2 / 8 * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    have h4 : (4 * σ * ε) ^ 2 / 8 = 2 * ε ^ 2 := by rw [mul_pow, mul_pow, hσ2]; ring
    rw [h4] at h3
    nlinarith [h2, h3, hℓe]
  have hsub : ∀ hT : Fin T → Trajectory S A H, (∃ t : ℕ,
      countSA ((List.ofFn hT).take t) h0.val s a = m + 1 ∧
      ε < |estExp ((List.ofFn hT).take t) h0.val s a f - c|) →
      ∃ b ∈ (Finset.univ : Finset Bool), (fun (b : Bool) hT => ∃ t : ℕ,
        countSA ((List.ofFn hT).take t) h0.val s a = m + 1 ∧
        ε < (if b then (1 : ℝ) else -1) *
          (estExp ((List.ofFn hT).take t) h0.val s a f - c)) b hT := by
    rintro hT ⟨t, ht, hdev⟩
    rcases lt_abs.mp hdev with h | h
    · exact ⟨true, Finset.mem_univ _, t, ht, by simpa using h⟩
    · exact ⟨false, Finset.mem_univ _, t, ht, by simpa using h⟩
  refine le_trans (probEvent_mono M learner hL T _ _ hsub)
    (le_trans (probEvent_exists_le M learner hL T _ _) ?_)
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  have := side 1 (Or.inl rfl)
  have := side (-1) (Or.inr rfl)
  linarith

end Conc

/-! ## Part 6. The UCB-VI estimates: bounds and optimism. -/

section Opt

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma ucbQ_eq (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ) (δ : ℝ) (T : ℕ)
    (l : List (Trajectory S A H)) (h : ℕ) (s : S) (a : A) :
    ucbQ M r δ T l h s a = if h < H then (if countSA l h s a = 0 then 1 else
      min 1 (r h s a + estExp l h s a (fun s' => ⨆ a', ucbQ M r δ T l (h + 1) s' a')
        + bonus δ (Fintype.card S) (Fintype.card A) H T (countSA l h s a))) else 0 := by
  rw [ucbQ]
  simp only [dite_eq_ite]

lemma estExp_eq (l : List (Trajectory S A H)) (h : ℕ) (s : S) (a : A) (f : S → ℝ)
    (hn : countSA l h s a ≠ 0) :
    estExp l h s a f = ∑ y, ((countSAS l h s a y : ℝ) / countSA l h s a) * f y := by
  simp only [estExp, hn, if_false]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma estExp_mono (l : List (Trajectory S A H)) (h : ℕ) (s : S) (a : A) (f g : S → ℝ)
    (hfg : ∀ y, f y ≤ g y) : estExp l h s a f ≤ estExp l h s a g := by
  by_cases hn : countSA l h s a = 0
  · simp [estExp, hn]
  · rw [estExp_eq l h s a f hn, estExp_eq l h s a g hn]
    exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hfg y) (by positivity))

lemma estExp_nonneg (l : List (Trajectory S A H)) (h : ℕ) (s : S) (a : A) (f : S → ℝ)
    (hf : ∀ y, 0 ≤ f y) : 0 ≤ estExp l h s a f := by
  have := estExp_mono l h s a (fun _ => 0) f hf
  refine le_trans (le_of_eq ?_) this
  by_cases hn : countSA l h s a = 0
  · simp [estExp, hn]
  · rw [estExp_eq l h s a _ hn]; simp

lemma bonus_nonneg (δ : ℝ) (a b c d n : ℕ) : 0 ≤ bonus δ a b c d n := by
  unfold bonus; positivity

lemma iSup_ge' {f : A → ℝ} (a : A) : f a ≤ ⨆ a', f a' :=
  le_ciSup (Set.finite_range _).bddAbove a

lemma ucbQ_bounds (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ) (δ : ℝ) (T : ℕ)
    (hr : ∀ h, h < H → ∀ s a, 0 ≤ r h s a ∧ r h s a ≤ 1) (l : List (Trajectory S A H)) :
    ∀ h s a, 0 ≤ ucbQ M r δ T l h s a ∧ ucbQ M r δ T l h s a ≤ 1 := by
  have main : ∀ k h, H - h = k → ∀ s a, 0 ≤ ucbQ M r δ T l h s a ∧ ucbQ M r δ T l h s a ≤ 1 := by
    intro k
    induction k with
    | zero =>
      intro h hk s a
      rw [ucbQ_eq, if_neg (by omega)]
      norm_num
    | succ k ih =>
      intro h hk s a
      have hh : h < H := by omega
      rw [ucbQ_eq, if_pos hh]
      split_ifs with hn
      · norm_num
      · have hV : ∀ s', 0 ≤ ⨆ a', ucbQ M r δ T l (h + 1) s' a' := fun s' =>
          le_trans (ih (h + 1) (by omega) s' (Classical.arbitrary A)).1 (iSup_ge' _)
        refine ⟨le_min zero_le_one ?_, min_le_left _ _⟩
        have := estExp_nonneg l h s a _ hV
        have := bonus_nonneg δ (Fintype.card S) (Fintype.card A) H T (countSA l h s a)
        linarith [(hr h hh s a).1]
  exact fun h s a => main (H - h) h rfl s a

lemma Qstar_ge (M : EpisodicMDP S A H) (h : ℕ) (hh : H ≤ h) (s : S) (a : A) :
    Qstar M h s a = 0 := by
  haveI : Nonempty {π : Policy S A H // IsPolicy H π} :=
    ⟨⟨detPolicy (fun _ _ => Classical.arbitrary A), detPolicy_isPolicy _⟩⟩
  unfold Qstar
  simp only [Q, if_neg (not_lt.mpr hh), ciSup_const]

/-- Optimism: under the `V⋆` concentration event at history `l`, `Q⋆ ≤ Q̄`. -/
theorem optimism (M : EpisodicMDP S A H) (δ : ℝ) (T : ℕ)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1)
    (hV1 : ∀ h, h < H → ∀ s, 0 ≤ Vstar M h s ∧ Vstar M h s ≤ 1)
    (l : List (Trajectory S A H))
    (hconc : ∀ h, h < H → ∀ s a, countSA l h s a ≠ 0 →
      |estExp l h s a (Vstar M (h + 1)) - ∑ y, M.P h s a y * Vstar M (h + 1) y| ≤
        bonus δ (Fintype.card S) (Fintype.card A) H T (countSA l h s a)) :
    ∀ h s a, Qstar M h s a ≤ ucbQ M M.R δ T l h s a := by
  have main : ∀ k h, H - h = k → ∀ s a, Qstar M h s a ≤ ucbQ M M.R δ T l h s a := by
    intro k
    induction k with
    | zero =>
      intro h hk s a
      rw [ucbQ_eq, if_neg (by omega), Qstar_ge M h (by omega)]
    | succ k ih =>
      intro h hk s a
      have hh : h < H := by omega
      have hQ1 : Qstar M h s a ≤ 1 := le_trans (Qstar_le_Vstar M h s a) (hV1 h hh s).2
      rw [ucbQ_eq, if_pos hh]
      split_ifs with hn
      · exact hQ1
      · refine le_min hQ1 ?_
        have hVV : ∀ y, Vstar M (h + 1) y ≤ ⨆ a', ucbQ M M.R δ T l (h + 1) y a' := fun y =>
          ciSup_mono (Set.finite_range _).bddAbove (fun a' => ih (h + 1) (by omega) y a')
        have h1 := Qstar_le M hR h hh s a
        have h2 := (abs_le.mp (hconc h hh s a hn)).1
        have h3 := estExp_mono l h s a _ _ hVV
        linarith
  exact fun h s a => main (H - h) h rfl s a

end Opt

/-! ## Part 7. The gap recursion and its unrolling along the played policy. -/

section Gap

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma det_sum (πd : ℕ → S → A) (h : ℕ) (x : S) (g : A → ℝ) :
    ∑ b, detPolicy (H := H) πd h x b * g b = g (πd h x) := by
  simp [detPolicy, ite_mul, Finset.sum_ite_eq']

noncomputable def Vb (M : EpisodicMDP S A H) (δ : ℝ) (T : ℕ) (l : List (Trajectory S A H))
    (h : ℕ) (s : S) : ℝ := ⨆ a, ucbQ M M.R δ T l h s a

/-- The per-layer surplus: `1` on an unvisited pair, else `min 1 (bonus + β n)`. -/
noncomputable def xi (δ : ℝ) (T : ℕ) (beta : ℕ → ℝ) (l : List (Trajectory S A H)) (h : ℕ)
    (s : S) (a : A) : ℝ :=
  if countSA l h s a = 0 then 1 else
    min 1 (bonus δ (Fintype.card S) (Fintype.card A) H T (countSA l h s a) + beta (countSA l h s a))

lemma xi_bounds (δ : ℝ) (T : ℕ) (beta : ℕ → ℝ) (hb : ∀ n, 0 ≤ beta n)
    (l : List (Trajectory S A H)) (h : ℕ) (s : S) (a : A) :
    0 ≤ xi δ T beta l h s a ∧ xi δ T beta l h s a ≤ 1 := by
  unfold xi
  split_ifs
  · norm_num
  · exact ⟨le_min zero_le_one (add_nonneg (bonus_nonneg _ _ _ _ _ _) (hb _)), min_le_left _ _⟩

theorem gap_step (M : EpisodicMDP S A H) (δ : ℝ) (T : ℕ) (beta : ℕ → ℝ)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1)
    (hV1 : ∀ h, h < H → ∀ s, 0 ≤ Vstar M h s ∧ Vstar M h s ≤ 1)
    (sel : ℕ → S → A) (l : List (Trajectory S A H))
    (hsel : ∀ h s, IsArgmax (ucbQ M M.R δ T l h s) (sel h s))
    (hconc : ∀ h, h < H → ∀ s a, countSA l h s a ≠ 0 →
      |estExp l h s a (Vstar M (h + 1)) - ∑ y, M.P h s a y * Vstar M (h + 1) y| ≤
        bonus δ (Fintype.card S) (Fintype.card A) H T (countSA l h s a))
    (hL1 : ∀ h, h < H → ∀ s a, countSA l h s a ≠ 0 → ∀ B : Finset S,
      estExp l h s a (fun y => if y ∈ B then 1 else 0) -
        ∑ y, M.P h s a y * (if y ∈ B then 1 else 0) ≤ beta (countSA l h s a))
    (h : ℕ) (hh : h < H) (x : S) :
    Vb M δ T l h x - V M (detPolicy (H := H) sel) h x ≤ xi δ T beta l h x (sel h x) +
      ∑ y, M.P h x (sel h x) y *
        (Vb M δ T l (h + 1) y - V M (detPolicy (H := H) sel) (h + 1) y) := by
  have hπ : IsPolicy H (detPolicy (H := H) sel) := detPolicy_isPolicy sel
  have hVb : Vb M δ T l h x = ucbQ M M.R δ T l h x (sel h x) := iSup_eq_of_argmax (hsel h x)
  have hV : V M (detPolicy (H := H) sel) h x = M.R h x (sel h x) +
      ∑ y, M.P h x (sel h x) y * V M (detPolicy (H := H) sel) (h + 1) y := by
    rw [V_lt M _ h hh x, det_sum]
    unfold Q
    rw [if_pos hh]
  have hopt := optimism M δ T hR hV1 l hconc
  have hVb1 : ∀ y, 0 ≤ Vb M δ T l (h + 1) y ∧ Vb M δ T l (h + 1) y ≤ 1 := by
    intro y
    rw [show Vb M δ T l (h + 1) y = ucbQ M M.R δ T l (h + 1) y (sel (h + 1) y) from
      iSup_eq_of_argmax (hsel (h + 1) y)]
    exact ucbQ_bounds M M.R δ T hR l _ _ _
  have hD' : ∀ y, 0 ≤ Vb M δ T l (h + 1) y - V M (detPolicy (H := H) sel) (h + 1) y := by
    intro y
    have h1 := V_le_Vstar M hR _ hπ (h + 1) y
    have h2 : Vstar M (h + 1) y ≤ Vb M δ T l (h + 1) y :=
      ciSup_mono (Set.finite_range _).bddAbove (fun a => hopt (h + 1) y a)
    linarith
  have hPD : 0 ≤ ∑ y, M.P h x (sel h x) y *
      (Vb M δ T l (h + 1) y - V M (detPolicy (H := H) sel) (h + 1) y) :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (M.P_nonneg _ _ _ _) (hD' y))
  have hPV : 0 ≤ ∑ y, M.P h x (sel h x) y * V M (detPolicy (H := H) sel) (h + 1) y :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (M.P_nonneg _ _ _ _) (V_nonneg M _ hπ hR _ y))
  have hQb := ucbQ_bounds M M.R δ T hR l h x (sel h x)
  have hr := hR h hh x (sel h x)
  rw [hVb, hV]
  unfold xi
  split_ifs with hn
  · linarith [hQb.2]
  · rw [← min_add_add_right]
    refine le_min (by linarith [hQb.2]) ?_
    have hQle : ucbQ M M.R δ T l h x (sel h x) ≤ M.R h x (sel h x) +
        estExp l h x (sel h x) (Vb M δ T l (h + 1)) +
        bonus δ (Fintype.card S) (Fintype.card A) H T (countSA l h x (sel h x)) := by
      rw [ucbQ_eq, if_pos hh, if_neg hn]
      exact min_le_right _ _
    set q : S → ℝ := fun y => (countSAS l h x (sel h x) y : ℝ) / countSA l h x (sel h x)
      with hqdef
    have hE : ∀ f : S → ℝ, estExp l h x (sel h x) f = ∑ y, q y * f y :=
      fun f => estExp_eq l h x (sel h x) f hn
    set B : Finset S := Finset.univ.filter (fun y => M.P h x (sel h x) y < q y) with hBdef
    have hB := hL1 h hh x (sel h x) hn B
    rw [hE] at hB hQle
    have key : ∑ y, q y * Vb M δ T l (h + 1) y -
        ∑ y, M.P h x (sel h x) y * Vb M δ T l (h + 1) y ≤
        ∑ y, q y * (if y ∈ B then 1 else 0) -
          ∑ y, M.P h x (sel h x) y * (if y ∈ B then 1 else 0) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : M.P h x (sel h x) y < q y
      · have hyB : y ∈ B := by simp [hBdef, hy]
        simp only [hyB, if_true, mul_one]
        nlinarith [(hVb1 y).2]
      · have hyB : y ∉ B := by simp [hBdef, hy]
        simp only [hyB, if_false, mul_zero, sub_zero]
        nlinarith [(hVb1 y).1]
    have expand : ∑ y, M.P h x (sel h x) y *
        (Vb M δ T l (h + 1) y - V M (detPolicy (H := H) sel) (h + 1) y) =
        ∑ y, M.P h x (sel h x) y * Vb M δ T l (h + 1) y -
          ∑ y, M.P h x (sel h x) y * V M (detPolicy (H := H) sel) (h + 1) y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [expand]
    linarith

lemma Vb_ge (M : EpisodicMDP S A H) (δ : ℝ) (T : ℕ) (l : List (Trajectory S A H)) (h : ℕ)
    (hh : H ≤ h) (s : S) : Vb M δ T l h s = 0 := by
  unfold Vb
  have hz : ∀ a, ucbQ M M.R δ T l h s a = 0 := fun a => by
    rw [ucbQ_eq, if_neg (not_lt.mpr hh)]
  simp only [hz, ciSup_const]

/-- Unrolled gap: the optimistic surplus of episode `l` is at most the expected sum of the
per-layer surpluses along the played trajectory. -/
theorem gap_unroll (M : EpisodicMDP S A H) (δ : ℝ) (T : ℕ) (beta : ℕ → ℝ)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1)
    (hV1 : ∀ h, h < H → ∀ s, 0 ≤ Vstar M h s ∧ Vstar M h s ≤ 1)
    (sel : ℕ → S → A) (l : List (Trajectory S A H))
    (hsel : ∀ h s, IsArgmax (ucbQ M M.R δ T l h s) (sel h s))
    (hconc : ∀ h, h < H → ∀ s a, countSA l h s a ≠ 0 →
      |estExp l h s a (Vstar M (h + 1)) - ∑ y, M.P h s a y * Vstar M (h + 1) y| ≤
        bonus δ (Fintype.card S) (Fintype.card A) H T (countSA l h s a))
    (hL1 : ∀ h, h < H → ∀ s a, countSA l h s a ≠ 0 → ∀ B : Finset S,
      estExp l h s a (fun y => if y ∈ B then 1 else 0) -
        ∑ y, M.P h s a y * (if y ∈ B then 1 else 0) ≤ beta (countSA l h s a)) :
    ∑ s, M.d1 s * (Vb M δ T l 0 s - V M (detPolicy (H := H) sel) 0 s) ≤
      ∑ τ, trajProb M (detPolicy (H := H) sel) τ *
        ∑ h ∈ Finset.range H, xi δ T beta l h (stateAt τ h) (actionAt τ h) := by
  have hπ : IsPolicy H (detPolicy (H := H) sel) := detPolicy_isPolicy sel
  set Δ : ℕ → S → ℝ := fun h s => Vb M δ T l h s - V M (detPolicy (H := H) sel) h s with hΔ
  have hstep : ∀ k (hk : k < H), ∑ τ, trajProb M (detPolicy (H := H) sel) τ * Δ k (stateAt τ k) ≤
      ∑ τ, trajProb M (detPolicy (H := H) sel) τ * xi δ T beta l k (stateAt τ k) (actionAt τ k) +
      ∑ τ, trajProb M (detPolicy (H := H) sel) τ * Δ (k + 1) (stateAt τ (k + 1)) := by
    intro k hk
    have m1 := traj_markov M _ hπ ⟨k, hk⟩ (fun x b _ => xi δ T beta l k x b)
    have m2 := traj_markov M _ hπ ⟨k, hk⟩ (fun _ _ y => Δ (k + 1) y)
    simp only at m1 m2
    simp only [stateAt_succ]
    rw [m1, m2, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro τ _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (trajProb_nonneg M _ hπ τ)
    simp only [det_sum]
    rw [← Finset.sum_mul, M.P_sum_one, one_mul]
    exact gap_step M δ T beta hR hV1 sel l hsel hconc hL1 k hk (stateAt τ k)
  have claim : ∀ k, k ≤ H →
      ∑ τ, trajProb M (detPolicy (H := H) sel) τ * Δ 0 (stateAt τ 0) ≤
        ∑ h ∈ Finset.range k, ∑ τ, trajProb M (detPolicy (H := H) sel) τ *
          xi δ T beta l h (stateAt τ h) (actionAt τ h) +
        ∑ τ, trajProb M (detPolicy (H := H) sel) τ * Δ k (stateAt τ k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have := hstep k (by omega)
      rw [Finset.sum_range_succ]
      linarith [ih (by omega)]
  have hH := claim H le_rfl
  have hzero : ∀ τ : Trajectory S A H, Δ H (stateAt τ H) = 0 := by
    intro τ
    simp only [hΔ, Vb_ge M δ T l H le_rfl, V_ge M _ H le_rfl, sub_zero]
  simp only [hzero, mul_zero, Finset.sum_const_zero, add_zero] at hH
  have hinit := traj_init M _ hπ (Δ 0)
  have e0 : ∀ τ : Trajectory S A H, stateAt τ 0 = τ.1 := fun τ => rfl
  simp only [e0] at hH
  rw [hinit] at hH
  refine le_trans hH (le_of_eq ?_)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.mul_sum]

end Gap

/-! ## Part 8. Azuma over episodes and the pigeonhole (potential) bound. -/

section Azuma

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma lsum_add (g w : List (Trajectory S A H) → Trajectory S A H → ℝ)
    (l : List (Trajectory S A H)) :
    lsum (fun l' τ => g l' τ + w l' τ) l = lsum g l + lsum w l := by
  have := lsum_lin g w 1 1 l
  simp only [one_mul] at this
  exact this

lemma lsum_one (l : List (Trajectory S A H)) :
    lsum (fun _ _ => (1 : ℝ)) l = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [lsum_nil]
  | append_singleton l τ ih =>
    rw [lsum_snoc, ih]
    simp

lemma lsum_finsum {ι : Type*} (s : Finset ι) (g : ι → List (Trajectory S A H) → Trajectory S A H → ℝ)
    (l : List (Trajectory S A H)) :
    lsum (fun l' τ => ∑ i ∈ s, g i l' τ) l = ∑ i ∈ s, lsum (g i) l := by
  induction l using List.reverseRecOn with
  | nil => simp [lsum_nil]
  | append_singleton l τ ih =>
    rw [lsum_snoc, ih]
    simp only [lsum_snoc, Finset.sum_add_distrib]

lemma lsum_prefix (g : List (Trajectory S A H) → ℝ) (l : List (Trajectory S A H)) :
    lsum (fun l' _ => g l') l = ∑ i ∈ Finset.range l.length, g (l.take i) := by
  induction l using List.reverseRecOn with
  | nil => simp [lsum_nil]
  | append_singleton l τ ih =>
    rw [lsum_snoc, ih, List.length_append, List.length_singleton, Finset.sum_range_succ,
      List.take_left' rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [List.take_append_of_le_length (by simp at hi; omega)]

lemma lsum_ofFn_prefix (g : List (Trajectory S A H) → ℝ) {T : ℕ}
    (hT : Fin T → Trajectory S A H) :
    lsum (fun l' _ => g l') (List.ofFn hT) = ∑ t : Fin T, g ((List.ofFn hT).take t.val) := by
  rw [lsum_prefix, List.length_ofFn, Fin.sum_univ_eq_sum_range (fun i => g ((List.ofFn hT).take i))]

/-- Azuma-Hoeffding over episodes for a `[0,c]`-valued per-episode functional. -/
theorem azuma (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (Y : List (Trajectory S A H) → Trajectory S A H → ℝ)
    (c : ℝ) (hc : 0 < c) (hY : ∀ l τ, Y l τ ∈ Set.Icc 0 c) (hT : 0 < T) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    probEvent M learner T (fun hT' => c * Real.sqrt (T * ℓ / 2) <
      lsum (fun l τ => (∑ τ', trajProb M (learner l) τ' * Y l τ') - Y l τ) (List.ofFn hT')) ≤
      Real.exp (-ℓ) := by
  set ε := c * Real.sqrt (T * ℓ / 2) with hεdef
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hε0 : 0 ≤ ε := by positivity
  have hε2 : ε ^ 2 = c ^ 2 * T * ℓ / 2 := by
    rw [hεdef, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  set lam := 4 * ε / (c ^ 2 * T) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  apply prob_lsum M learner hL T _
    (fun l τ => lam * ((∑ τ', trajProb M (learner l) τ' * Y l τ') - Y l τ)
      + (-(lam ^ 2 * c ^ 2 / 8)) * 1) _ ℓ
  · rintro hT' hdev
    rw [lsum_lin, lsum_one, List.length_ofFn]
    have h1 : lam * ε ≤ lam * lsum (fun l τ => (∑ τ', trajProb M (learner l) τ' * Y l τ') - Y l τ)
        (List.ofFn hT') := mul_le_mul_of_nonneg_left hdev.le hlam0
    have h2 : lam * ε - lam ^ 2 * c ^ 2 / 8 * T = 2 * ε ^ 2 / (c ^ 2 * T) := by
      rw [hlam]
      field_simp
      ring
    have h3 : 2 * ε ^ 2 / (c ^ 2 * T) = ℓ := by
      rw [hε2]
      field_simp
    nlinarith [h1, h2, h3]
  · intro l
    have hp0 := fun τ => trajProb_nonneg M (learner l) (hL l) τ
    have hh := hoeffding_fin (trajProb M (learner l)) hp0 (sum_trajProb M _ (hL l)) (Y l) 0 c
      (hY l) (-lam)
    calc ∑ τ, trajProb M (learner l) τ *
          Real.exp (lam * ((∑ τ', trajProb M (learner l) τ' * Y l τ') - Y l τ)
            + (-(lam ^ 2 * c ^ 2 / 8)) * 1)
        = (∑ τ, trajProb M (learner l) τ *
            Real.exp (-lam * (Y l τ - ∑ τ', trajProb M (learner l) τ' * Y l τ'))) *
            Real.exp (-(lam ^ 2 * c ^ 2 / 8)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro τ _
          rw [mul_one, mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ Real.exp ((-lam) ^ 2 * (c - 0) ^ 2 / 8) * Real.exp (-(lam ^ 2 * c ^ 2 / 8)) :=
          mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add]
          norm_num

lemma sum_sqrt_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, Real.sqrt (a i) ≤ Real.sqrt (s.card * ∑ i ∈ s, a i) := by
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => Real.sqrt (a i))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have e : ∑ i ∈ s, Real.sqrt (a i) ^ 2 = ∑ i ∈ s, a i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (ha i hi))
  rw [e] at h
  exact h


/-- Potential for the pigeonhole bound. -/
noncomputable def phiP (c : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else 1 + 2 * c * Real.sqrt ((N : ℝ) - 1)

lemma phi_step (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (v : ℝ) (hv1 : v ≤ 1)
    (hv : n ≠ 0 → v ≤ c / Real.sqrt n) : v ≤ phiP c (n + 1) - phiP c n := by
  unfold phiP
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.zero_add, one_ne_zero, if_false, if_true, Nat.cast_one, sub_self,
      Real.sqrt_zero, mul_zero, add_zero, sub_zero]
    exact hv1
  · rw [if_neg (Nat.succ_ne_zero n), if_neg hn]
    have hv' := hv hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    push_cast
    rw [add_sub_cancel_right]
    set a := Real.sqrt (n : ℝ) with ha
    set b := Real.sqrt ((n : ℝ) - 1) with hb
    have ha2 : a ^ 2 = n := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
    have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hab : 2 * a * b ≤ 2 * (n : ℝ) - 1 := by nlinarith [sq_nonneg (a - b)]
    have key : c / a ≤ 2 * c * (a - b) := by
      rw [div_le_iff₀ ha0]
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hab)]
    linarith

lemma sum_countSA (h : ℕ) (l : List (Trajectory S A H)) :
    ∑ p : S × A, (countSA l h p.1 p.2 : ℝ) = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [countSA]
  | append_singleton l τ ih =>
    simp only [countSA_snoc]
    push_cast
    rw [Finset.sum_add_distrib, ih]
    have e : ∀ p : S × A, ((if stateAt τ h = p.1 ∧ actionAt τ h = p.2 then (1 : ℝ) else 0)) =
        if (stateAt τ h, actionAt τ h) = p then 1 else 0 := by
      intro p
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
      · rintro rfl; exact ⟨rfl, rfl⟩
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, e, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    simp

/-- Pigeonhole via the potential `phiP`: the running sum of per-visit surpluses at layer `h`
is bounded by the final potential. -/
theorem pigeon_layer (c : ℝ) (h : ℕ) (g : ℕ → ℝ) (hg : ∀ n, g n ≤ phiP c (n + 1) - phiP c n)
    (l : List (Trajectory S A H)) :
    lsum (fun l' τ => g (countSA l' h (stateAt τ h) (actionAt τ h))) l ≤
      ∑ p : S × A, phiP c (countSA l h p.1 p.2) := by
  induction l using List.reverseRecOn with
  | nil => simp [lsum_nil, countSA, phiP]
  | append_singleton l τ ih =>
    rw [lsum_snoc]
    set p0 : S × A := (stateAt τ h, actionAt τ h)
    have hdiff : ∑ p : S × A, phiP c (countSA (l ++ [τ]) h p.1 p.2) -
        ∑ p : S × A, phiP c (countSA l h p.1 p.2) =
        phiP c (countSA l h p0.1 p0.2 + 1) - phiP c (countSA l h p0.1 p0.2) := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single p0]
      · rw [countSA_snoc, if_pos ⟨rfl, rfl⟩]
      · intro p _ hp
        have hne : ¬ (stateAt τ h = p.1 ∧ actionAt τ h = p.2) := by
          rintro ⟨h1, h2⟩
          exact hp (Prod.ext h1.symm h2.symm)
        rw [countSA_snoc, if_neg hne, add_zero, sub_self]
      · intro hp; exact absurd (Finset.mem_univ p0) hp
    have := hg (countSA l h p0.1 p0.2)
    linarith

lemma phi_total (c : ℝ) (hc : 0 ≤ c) (h : ℕ) (l : List (Trajectory S A H)) :
    ∑ p : S × A, phiP c (countSA l h p.1 p.2) ≤
      (Fintype.card S * Fintype.card A : ℝ) +
        2 * c * Real.sqrt ((Fintype.card S * Fintype.card A : ℝ) * l.length) := by
  have h1 : ∀ p : S × A, phiP c (countSA l h p.1 p.2) ≤
      1 + 2 * c * Real.sqrt (countSA l h p.1 p.2 : ℝ) := by
    intro p
    unfold phiP
    split_ifs
    · positivity
    · have : Real.sqrt ((countSA l h p.1 p.2 : ℝ) - 1) ≤ Real.sqrt (countSA l h p.1 p.2 : ℝ) :=
        Real.sqrt_le_sqrt (by linarith)
      nlinarith
  have h2 := sum_sqrt_le (Finset.univ : Finset (S × A)) (fun p => (countSA l h p.1 p.2 : ℝ))
    (fun p _ => by positivity)
  rw [sum_countSA, Finset.card_univ, Fintype.card_prod] at h2
  push_cast at h2
  calc ∑ p : S × A, phiP c (countSA l h p.1 p.2)
      ≤ ∑ p : S × A, (1 + 2 * c * Real.sqrt (countSA l h p.1 p.2 : ℝ)) :=
        Finset.sum_le_sum (fun p _ => h1 p)
    _ = (Fintype.card S * Fintype.card A : ℝ) +
          2 * c * ∑ p : S × A, Real.sqrt (countSA l h p.1 p.2 : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [Fintype.card_prod]
    _ ≤ _ := by nlinarith [h2]

end Azuma

/-! ## Part 9a. Union bounds and numerics. -/

section Union

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma countSA_le_length (l : List (Trajectory S A H)) (h : ℕ) (s : S) (a : A) :
    countSA l h s a ≤ l.length := List.length_filter_le _ _

theorem conc_union (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) {ι : Type*} [Fintype ι]
    (F : Fin H → ι → S → ℝ) (hF : ∀ h0 i y, F h0 i y ∈ Set.Icc (0 : ℝ) 1) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    probEvent M learner T (fun hT => ∃ t : ℕ, ∃ h0 : Fin H, ∃ s : S, ∃ a : A, ∃ i : ι,
      countSA ((List.ofFn hT).take t) h0.val s a ≠ 0 ∧
      Real.sqrt (ℓ / (2 * (countSA ((List.ofFn hT).take t) h0.val s a : ℝ))) <
        |estExp ((List.ofFn hT).take t) h0.val s a (F h0 i) -
          ∑ y, M.P h0.val s a y * F h0 i y|) ≤
      ((H : ℝ) * Fintype.card S * Fintype.card A * Fintype.card ι * T) * (2 * Real.exp (-ℓ)) := by
  classical
  let B : Fin H × S × A × ι × Fin T → (Fin T → Trajectory S A H) → Prop := fun x hT =>
    ∃ t : ℕ, countSA ((List.ofFn hT).take t) x.1.val x.2.1 x.2.2.1 = x.2.2.2.2.val + 1 ∧
      Real.sqrt (ℓ / (2 * ((x.2.2.2.2.val : ℝ) + 1))) <
        |estExp ((List.ofFn hT).take t) x.1.val x.2.1 x.2.2.1 (F x.1 x.2.2.2.1) -
          ∑ y, M.P x.1.val x.2.1 x.2.2.1 y * F x.1 x.2.2.2.1 y|
  have hsub : ∀ hT : Fin T → Trajectory S A H, (∃ t : ℕ, ∃ h0 : Fin H, ∃ s : S, ∃ a : A,
      ∃ i : ι, countSA ((List.ofFn hT).take t) h0.val s a ≠ 0 ∧
      Real.sqrt (ℓ / (2 * (countSA ((List.ofFn hT).take t) h0.val s a : ℝ))) <
        |estExp ((List.ofFn hT).take t) h0.val s a (F h0 i) -
          ∑ y, M.P h0.val s a y * F h0 i y|) →
      ∃ x ∈ (Finset.univ : Finset (Fin H × S × A × ι × Fin T)), B x hT := by
    rintro hT ⟨t, h0, s, a, i, hn, hdev⟩
    have hnT : countSA ((List.ofFn hT).take t) h0.val s a ≤ T :=
      le_trans (countSA_le_length _ _ _ _) (by
        rw [List.length_take, List.length_ofFn]; exact min_le_right _ _)
    refine ⟨(h0, s, a, i, ⟨countSA ((List.ofFn hT).take t) h0.val s a - 1, by omega⟩),
      Finset.mem_univ _, t, ?_, ?_⟩
    · dsimp only
      omega
    · dsimp only
      have hc : (((countSA ((List.ofFn hT).take t) h0.val s a - 1 : ℕ) : ℝ) + 1) =
          (countSA ((List.ofFn hT).take t) h0.val s a : ℝ) := by
        have : countSA ((List.ofFn hT).take t) h0.val s a - 1 + 1 =
            countSA ((List.ofFn hT).take t) h0.val s a := by omega
        exact_mod_cast this
      rw [hc]
      exact hdev
  refine le_trans (probEvent_mono M learner hL T _ _ hsub)
    (le_trans (probEvent_exists_le M learner hL T _ _) ?_)
  refine le_trans (Finset.sum_le_sum (fun x _ => conc_event M learner hL T x.1 x.2.1 x.2.2.1
    x.2.2.2.2.val (F x.1 x.2.2.2.1) (hF _ _) ℓ hℓ)) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

lemma probEvent_or (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (E F : (Fin T → Trajectory S A H) → Prop) :
    probEvent M learner T (fun h => E h ∨ F h) ≤
      probEvent M learner T E + probEvent M learner T F := by
  classical
  unfold probEvent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h _
  have h0 := historyProb_nonneg M learner hL h
  by_cases h1 : E h <;> by_cases h2 : F h <;> simp [h1, h2] <;> linarith

lemma probEvent_all (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (E : (Fin T → Trajectory S A H) → Prop)
    (hE : ∀ h, E h) : probEvent M learner T E = 1 := by
  classical
  unfold probEvent
  simp only [hE, if_true]
  exact hist_total M learner hL T

end Union

lemma sqrt_le_of_sq (x y : ℝ) (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y := by
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

lemma c_bound (L0 L1 ℓ2 s : ℝ) (hL0 : 0 ≤ L0) (hs : 1 ≤ s) (hL1 : L1 ≤ 2 * L0)
    (hℓ2 : ℓ2 ≤ 5 * s * L0) :
    2 * Real.sqrt L1 + Real.sqrt (ℓ2 / 2) ≤ 5 * Real.sqrt s * Real.sqrt L0 := by
  have hq0 := Real.sqrt_nonneg L0
  have hq2 := Real.sq_sqrt hL0
  have hσ1 : 1 ≤ Real.sqrt s := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hs
  have hσ2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ s)
  have h1 : Real.sqrt L1 ≤ 3 / 2 * Real.sqrt L0 :=
    sqrt_le_of_sq _ _ (by positivity) (by nlinarith)
  have h2 : Real.sqrt (ℓ2 / 2) ≤ 8 / 5 * Real.sqrt s * Real.sqrt L0 :=
    sqrt_le_of_sq _ _ (by positivity) (by
      have : (8 / 5 * Real.sqrt s * Real.sqrt L0) ^ 2 = 64 / 25 * s * L0 := by
        rw [mul_pow, mul_pow, hσ2, hq2]; ring
      rw [this]; nlinarith)
  nlinarith [mul_le_mul_of_nonneg_right hσ1 hq0]

lemma z_bound (T L0 ℓ3 : ℝ) (hT : 0 ≤ T) (hL0 : 0 ≤ L0) (hℓ3 : ℓ3 ≤ 3 * L0) :
    Real.sqrt (T * ℓ3 / 2) ≤ 5 / 4 * Real.sqrt T * Real.sqrt L0 := by
  apply sqrt_le_of_sq _ _ (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt hT, Real.sq_sqrt hL0]
  nlinarith

lemma final_numeric (h s a t q c σ u w z r : ℝ) (hh : 1 ≤ h) (hs : 1 ≤ s) (ha : 1 ≤ a)
    (ht : 1 ≤ t) (hq : 4 / 5 ≤ q) (hσ : 0 ≤ σ) (hσ2 : σ ^ 2 = s) (hu : 0 ≤ u)
    (hu2 : u ^ 2 = a * t) (hw : 0 ≤ w) (hw2 : w ^ 2 = t) (hc0 : 0 ≤ c) (hc : c ≤ 5 * σ * q)
    (hz : z ≤ 5 / 4 * w * q) (hr1 : r ≤ t) (hr2 : r ≤ h * (s * a + 2 * c * (σ * u)) + h * z) :
    r ≤ 30 * h * s * u * q := by
  have hwu : w ≤ u := by
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_lt_mul'' hlt hlt hu hu]
  have hu1 : 1 ≤ u := by
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_lt_mul'' hlt hlt hu hu]
  have hsu : 0 ≤ h * s * u := by positivity
  have hmin : r ≤ h * s * u + h * (2 * c * (σ * u)) + h * z ∨ r ≤ h * s * u := by
    by_cases hc1 : h * s * a ≤ t
    · left
      have hhs : 1 ≤ h * s := by nlinarith
      have hat : a ≤ t := by nlinarith [mul_le_mul_of_nonneg_right hhs (by linarith : (0:ℝ) ≤ a)]
      have hau : a ≤ u := by
        by_contra hlt
        push_neg at hlt
        nlinarith [mul_lt_mul'' hlt hlt hu hu]
      have : h * (s * a) ≤ h * (s * u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hau (by linarith)) (by linarith)
      nlinarith
    · right
      push_neg at hc1
      have htu : t ≤ h * s * u := by
        by_contra hlt
        push_neg at hlt
        have e1 : (h * s * u) * (h * s * u) < t * t := mul_lt_mul'' hlt hlt hsu hsu
        have e2 : (h * s * u) * (h * s * u) = (h * s) * (h * s) * (a * t) := by
          rw [← hu2]; ring
        have e3 : t * t < h * s * a * t := by nlinarith
        have e4 : h * s * a * t ≤ (h * s) * (h * s) * (a * t) := by
          have : 1 ≤ h * s := by nlinarith
          have : 0 ≤ a * t := by positivity
          nlinarith
        linarith
      linarith
  have hq0 : 0 ≤ q := by linarith
  have b1 : h * s * u ≤ 5 / 4 * (h * s * u * q) := by nlinarith
  have b2 : h * (2 * c * (σ * u)) ≤ 10 * (h * s * u * q) := by
    have : 2 * c * (σ * u) ≤ 2 * (5 * σ * q) * (σ * u) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : 2 * (5 * σ * q) * (σ * u) = 10 * (s * u * q) := by rw [← hσ2]; ring
    nlinarith
  have b3 : h * z ≤ 5 / 4 * (h * s * u * q) := by
    have : w * q ≤ s * u * q := by
      apply mul_le_mul_of_nonneg_right _ hq0
      nlinarith
    nlinarith
  have hpos : 0 ≤ h * s * u * q := by positivity
  rcases hmin with hm | hm <;> nlinarith

/-! ## Part 9b. Assembly. -/

section Main

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma regret_zero_deg (M : EpisodicMDP S A H) (learner : Learner S A H)
    (hL : ∀ l, IsPolicy H (learner l)) (T : ℕ) (hT : Fin T → Trajectory S A H)
    (hdeg : H = 0 ∨ (H = 1 ∧ Fintype.card A = 1)) :
    FoundationsRL.TabularRL.regret M learner T hT = 0 := by
  unfold FoundationsRL.TabularRL.regret
  apply Finset.sum_eq_zero
  intro t _
  rw [sub_eq_zero]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rcases hdeg with h0 | ⟨h1, hA⟩
  · rw [Vstar_ge M 0 (by omega) s, V_ge M _ 0 (by omega) s]
  · subst h1
    haveI : Nonempty {π : Policy S A 1 // IsPolicy 1 π} :=
      ⟨⟨detPolicy (fun _ _ => Classical.arbitrary A), detPolicy_isPolicy _⟩⟩
    have hsub : ∀ a b : A, a = b := Fintype.card_le_one_iff.mp hA.le
    set a0 := Classical.arbitrary A
    have hQ : ∀ π : Policy S A 1, ∀ a, Q M π 0 s a = M.R 0 s a := by
      intro π a
      simp only [Q, if_pos zero_lt_one, V_ge M π 1 le_rfl, mul_zero, Finset.sum_const_zero,
        add_zero]
    have hQs : ∀ a, Qstar M 0 s a = M.R 0 s a0 := by
      intro a
      unfold Qstar
      simp only [hQ, ciSup_const, hsub a a0]
    have hfun : (fun a => Qstar M 0 s a) = fun _ => M.R 0 s a0 := funext hQs
    unfold Vstar
    rw [hfun, ciSup_const, V_lt M _ 0 zero_lt_one s]
    simp only [hQ]
    have e : ∀ a, M.R 0 s a = M.R 0 s a0 := fun a => by rw [hsub a a0]
    simp only [e]
    rw [← Finset.sum_mul, (hL _ 0 zero_lt_one s).2, one_mul]

set_option maxHeartbeats 2000000 in
theorem main_fixed (M : EpisodicMDP S A H) (T : ℕ) (δ : ℝ) (learner : Learner S A H)
    (hδ : 0 < δ)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1)
    (hV1 : ∀ h, h < H → ∀ s, 0 ≤ Vstar M h s ∧ Vstar M h s ≤ 1)
    (hU : IsUCBVI M M.R δ T learner) :
    1 - δ ≤ probEvent M learner T (fun histT =>
      FoundationsRL.TabularRL.regret M learner T histT ≤
        30 * H * Fintype.card S * Real.sqrt (Fintype.card A * T) *
          Real.sqrt (Real.log (Fintype.card S * Fintype.card A * H * T / δ))) := by
  obtain ⟨sel, hsel, hlearn⟩ := hU
  have hL : ∀ l, IsPolicy H (learner l) := fun l => by rw [hlearn]; exact detPolicy_isPolicy _
  set RHS : ℝ := 30 * H * Fintype.card S * Real.sqrt (Fintype.card A * T) *
    Real.sqrt (Real.log (Fintype.card S * Fintype.card A * H * T / δ)) with hRHSdef
  have hRHS : 0 ≤ RHS := by positivity
  by_cases hδ1 : 1 ≤ δ
  · linarith [probEvent_nonneg M learner hL T (fun histT =>
      FoundationsRL.TabularRL.regret M learner T histT ≤ RHS)]
  push_neg at hδ1
  by_cases hdeg : H = 0 ∨ T = 0 ∨ (H = 1 ∧ Fintype.card A = 1)
  · have hall : ∀ histT, FoundationsRL.TabularRL.regret M learner T histT ≤ RHS := by
      intro histT
      have : FoundationsRL.TabularRL.regret M learner T histT = 0 := by
        rcases hdeg with h0 | hT0 | h1
        · exact regret_zero_deg M learner hL T histT (Or.inl h0)
        · subst hT0
          simp [FoundationsRL.TabularRL.regret]
        · exact regret_zero_deg M learner hL T histT (Or.inr h1)
      rw [this]
      exact hRHS
    rw [probEvent_all M learner hL T _ hall]
    linarith
  push_neg at hdeg
  obtain ⟨hH0, hT0, hdeg1⟩ := hdeg
  haveI := nonempty_of_M M
  have hSn : 1 ≤ Fintype.card S := Fintype.card_pos
  have hAn : 1 ≤ Fintype.card A := Fintype.card_pos
  have hHn : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr hH0
  have hTn : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT0
  have hN2n : 2 ≤ Fintype.card S * Fintype.card A * H * T := by
    rcases (by omega : H = 1 ∨ 2 ≤ H) with h1 | h2
    · have hA2 : 2 ≤ Fintype.card A := by have := hdeg1 h1; omega
      calc 2 = 1 * 2 * 1 * 1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hSn hA2) hHn) hTn
    · calc 2 = 1 * 1 * 2 * 1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hSn hAn) h2) hTn
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast hSn
  have hA1 : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast hAn
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hHn
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hTn
  have hN2 : (2 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A * H * T := by exact_mod_cast hN2n
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (Fintype.card S : ℝ) * Fintype.card A * H * T := ⟨_, rfl⟩
  rw [← hNdef] at hN2
  have hN0 : 0 < N := by linarith
  have hNd : 2 ≤ N / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have hNd0 : 0 < N / δ := by positivity
  have hlog2 := Real.log_two_gt_d9
  have hlog2p : 0 < Real.log 2 := by linarith
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have : Real.log 3 ≤ Real.log (2 ^ 2) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlog6 : Real.log 6 ≤ 3 * Real.log 2 := by
    have : Real.log 6 ≤ Real.log (2 ^ 3) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at this; push_cast at this; linarith
  -- the logarithms
  obtain ⟨L0, hL0def⟩ : ∃ x : ℝ, x = Real.log (N / δ) := ⟨_, rfl⟩
  have hL0 : Real.log 2 ≤ L0 := by rw [hL0def]; exact Real.log_le_log (by norm_num) hNd
  have hL0n : 0 ≤ L0 := by linarith
  obtain ⟨L1, hL1def⟩ : ∃ x : ℝ, x = Real.log (2 * (Fintype.card S : ℝ) * Fintype.card A * H * T / δ) :=
    ⟨_, rfl⟩
  have hL1eq : L1 = Real.log 2 + L0 := by
    rw [hL1def, hL0def, ← Real.log_mul (by norm_num) hNd0.ne', hNdef]
    congr 1
    ring
  obtain ⟨ℓ1, hℓ1def⟩ : ∃ x : ℝ, x = Real.log (6 * N / δ) := ⟨_, rfl⟩
  have hℓ1eq : ℓ1 = Real.log 3 + L1 := by
    rw [hℓ1def, hL1eq, hL0def, ← Real.log_mul (by norm_num) hNd0.ne',
      ← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  obtain ⟨ℓ2, hℓ2def⟩ : ∃ x : ℝ, x = Real.log (6 * 2 ^ Fintype.card S * N / δ) := ⟨_, rfl⟩
  have hℓ2eq : ℓ2 = Real.log 6 + Fintype.card S * Real.log 2 + L0 := by
    rw [hℓ2def, hL0def, ← Real.log_pow, ← Real.log_mul (by norm_num) (by positivity),
      ← Real.log_mul (by positivity) hNd0.ne']
    congr 1
    ring
  obtain ⟨ℓ3, hℓ3def⟩ : ∃ x : ℝ, x = Real.log (3 / δ) := ⟨_, rfl⟩
  have hℓ3le : ℓ3 ≤ 3 * L0 := by
    have h1 : ℓ3 ≤ Real.log (2 ^ 2 * (N / δ)) := by
      rw [hℓ3def]
      apply Real.log_le_log (by positivity)
      rw [show (2 : ℝ) ^ 2 * (N / δ) = 4 * N / δ by ring]
      exact div_le_div_of_nonneg_right (by linarith) hδ.le
    rw [Real.log_mul (by positivity) hNd0.ne', Real.log_pow, ← hL0def] at h1
    push_cast at h1
    linarith
  have hℓ1n : 0 ≤ ℓ1 := by rw [hℓ1eq, hL1eq]; linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
  have hℓ2n : 0 ≤ ℓ2 := by
    rw [hℓ2eq]
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 6)
    have : 0 ≤ (Fintype.card S : ℝ) * Real.log 2 := by positivity
    linarith
  have hℓ3n : 0 ≤ ℓ3 := by
    rw [hℓ3def]; apply Real.log_nonneg; rw [le_div_iff₀ hδ]; linarith
  have hL1n : 0 ≤ L1 := by rw [hL1eq]; linarith
  -- the three bad events
  set beta : ℕ → ℝ := fun n => Real.sqrt (ℓ2 / (2 * n)) with hbeta
  set Ylist : List (Trajectory S A H) → Trajectory S A H → ℝ := fun l τ =>
    ∑ h ∈ Finset.range H, xi δ T beta l h (stateAt τ h) (actionAt τ h) with hYlist
  have hF1 : ∀ (h0 : Fin H) (_ : Unit) (y : S), Vstar M (h0.val + 1) y ∈ Set.Icc (0 : ℝ) 1 := by
    intro h0 _ y
    by_cases hh : h0.val + 1 < H
    · exact hV1 _ hh y
    · rw [Vstar_ge M _ (by omega) y]; norm_num
  have hF2 : ∀ (h0 : Fin H) (B : Finset S) (y : S),
      (fun (_ : Fin H) (B : Finset S) (y : S) => if y ∈ B then (1 : ℝ) else 0) h0 B y ∈
        Set.Icc (0 : ℝ) 1 := by
    intro h0 B y
    dsimp only
    split_ifs <;> norm_num
  have hP1 := conc_union M learner hL T (fun h0 (_ : Unit) => Vstar M (h0.val + 1)) hF1 ℓ1 hℓ1n
  have hP2 := conc_union M learner hL T
    (fun (_ : Fin H) (B : Finset S) (y : S) => if y ∈ B then (1 : ℝ) else 0) hF2 ℓ2 hℓ2n
  have hYb : ∀ l τ, Ylist l τ ∈ Set.Icc (0 : ℝ) H := by
    intro l τ
    have hb : ∀ n, 0 ≤ beta n := fun n => Real.sqrt_nonneg _
    constructor
    · exact Finset.sum_nonneg (fun h _ => (xi_bounds δ T beta hb l h _ _).1)
    · calc Ylist l τ ≤ ∑ h ∈ Finset.range H, (1 : ℝ) :=
            Finset.sum_le_sum (fun h _ => (xi_bounds δ T beta hb l h _ _).2)
        _ = H := by simp
  have hP3 := azuma M learner hL T Ylist H (by positivity) hYb (by omega) ℓ3 hℓ3n
  -- probabilities
  have hP1' : (H * Fintype.card S * Fintype.card A * Fintype.card Unit * T : ℝ) *
      (2 * Real.exp (-ℓ1)) = δ / 3 := by
    rw [hℓ1def, Real.exp_neg, Real.exp_log (by positivity), Fintype.card_unit, hNdef]
    field_simp
    ring
  have hP2' : (H * Fintype.card S * Fintype.card A * Fintype.card (Finset S) * T : ℝ) *
      (2 * Real.exp (-ℓ2)) = δ / 3 := by
    rw [hℓ2def, Real.exp_neg, Real.exp_log (by positivity), Fintype.card_finset, hNdef]
    push_cast
    field_simp
    ring
  have hP3' : Real.exp (-ℓ3) = δ / 3 := by
    rw [hℓ3def, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hP1'] at hP1
  rw [hP2'] at hP2
  rw [hP3'] at hP3
  obtain ⟨cc, hccdef⟩ : ∃ x : ℝ, x = 2 * Real.sqrt L1 + Real.sqrt (ℓ2 / 2) := ⟨_, rfl⟩
  have hcc0 : 0 ≤ cc := by rw [hccdef]; positivity
  have hor := le_trans (probEvent_or M learner hL T _ _)
    (add_le_add hP1 (le_trans (probEvent_or M learner hL T _ _) (add_le_add hP2 hP3)))
  set E : (Fin T → Trajectory S A H) → Prop := fun histT =>
    FoundationsRL.TabularRL.regret M learner T histT ≤ RHS with hEdef
  have hbad : probEvent M learner T (fun h => ¬ E h) ≤ δ / 3 + (δ / 3 + δ / 3) := by
    refine le_trans (probEvent_mono M learner hL T (fun h => ¬ E h) _ ?_) hor
    intro histT hnE
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hn1, hn2, hn3⟩ := hcon
    simp only [not_exists, not_and, not_lt] at hn1 hn2 hn3
    apply hnE
    show FoundationsRL.TabularRL.regret M learner T histT ≤ RHS
    have hc1 : ∀ t : ℕ, ∀ h, h < H → ∀ s a, countSA ((List.ofFn histT).take t) h s a ≠ 0 →
        |estExp ((List.ofFn histT).take t) h s a (Vstar M (h + 1)) -
          ∑ y, M.P h s a y * Vstar M (h + 1) y| ≤
        bonus δ (Fintype.card S) (Fintype.card A) H T (countSA ((List.ofFn histT).take t) h s a) := by
      intro t h hh s a hn
      refine le_trans (hn1 t ⟨h, hh⟩ s a () hn) ?_
      have hnpos : (0 : ℝ) < countSA ((List.ofFn histT).take t) h s a := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      unfold bonus
      rw [← hL1def]
      apply sqrt_le_of_sq _ _ (by positivity)
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hℓL : ℓ1 ≤ 8 * L1 := by rw [hℓ1eq]; rw [hL1eq]; linarith only [hlog3, hL0, hlog2]
      calc ℓ1 / (2 * (countSA ((List.ofFn histT).take t) h s a : ℝ))
          = (ℓ1 / 2) / (countSA ((List.ofFn histT).take t) h s a : ℝ) := by ring
        _ ≤ (4 * L1) / (countSA ((List.ofFn histT).take t) h s a : ℝ) := by
          gcongr; linarith only [hℓL]
        _ = 2 ^ 2 * (L1 / (countSA ((List.ofFn histT).take t) h s a : ℝ)) := by ring
    have hc2 : ∀ t : ℕ, ∀ h, h < H → ∀ s a, countSA ((List.ofFn histT).take t) h s a ≠ 0 →
        ∀ B : Finset S, estExp ((List.ofFn histT).take t) h s a (fun y => if y ∈ B then 1 else 0) -
          ∑ y, M.P h s a y * (if y ∈ B then 1 else 0) ≤
          beta (countSA ((List.ofFn histT).take t) h s a) :=
      fun t h hh s a hn B => le_trans (le_abs_self _) (hn2 t ⟨h, hh⟩ s a B hn)
    have hterm : ∀ t : Fin T, (∑ s, M.d1 s * Vstar M 0 s -
        ∑ s, M.d1 s * V M (learner ((List.ofFn histT).take t.val)) 0 s) ≤
        ∑ τ, trajProb M (learner ((List.ofFn histT).take t.val)) τ *
          Ylist ((List.ofFn histT).take t.val) τ := by
      intro t
      rw [hlearn ((List.ofFn histT).take t.val)]
      have hu := gap_unroll M δ T beta hR hV1 (sel ((List.ofFn histT).take t.val))
        ((List.ofFn histT).take t.val) (hsel _) (hc1 t.val) (hc2 t.val)
      have hopt0 : ∀ s, Vstar M 0 s ≤ Vb M δ T ((List.ofFn histT).take t.val) 0 s := fun s =>
        ciSup_mono (Set.finite_range _).bddAbove
          (fun a => optimism M δ T hR hV1 _ (hc1 t.val) 0 s a)
      refine le_trans ?_ hu
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro s _
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left (by linarith only [hopt0 s]) (M.d1_nonneg s)
    have hterm1 : ∀ t : Fin T, (∑ s, M.d1 s * Vstar M 0 s -
        ∑ s, M.d1 s * V M (learner ((List.ofFn histT).take t.val)) 0 s) ≤ 1 := by
      intro t
      have h1 : ∑ s, M.d1 s * Vstar M 0 s ≤ 1 := by
        calc ∑ s, M.d1 s * Vstar M 0 s ≤ ∑ s, M.d1 s * 1 :=
              Finset.sum_le_sum (fun s _ =>
                mul_le_mul_of_nonneg_left (hV1 0 (by omega) s).2 (M.d1_nonneg s))
          _ = 1 := by simp [M.d1_sum_one]
      have h2 : 0 ≤ ∑ s, M.d1 s * V M (learner ((List.ofFn histT).take t.val)) 0 s :=
        Finset.sum_nonneg (fun s _ => mul_nonneg (M.d1_nonneg s) (V_nonneg M _ (hL _) hR 0 s))
      linarith only [h1, h2]
    have hregT : FoundationsRL.TabularRL.regret M learner T histT ≤ T := by
      unfold FoundationsRL.TabularRL.regret
      calc _ ≤ ∑ t : Fin T, (1 : ℝ) := Finset.sum_le_sum (fun t _ => hterm1 t)
        _ = T := by simp
    have hregX : FoundationsRL.TabularRL.regret M learner T histT ≤
        lsum Ylist (List.ofFn histT) +
          lsum (fun l τ => (∑ τ', trajProb M (learner l) τ' * Ylist l τ') - Ylist l τ)
            (List.ofFn histT) := by
      unfold FoundationsRL.TabularRL.regret
      calc _ ≤ ∑ t : Fin T, (∑ τ, trajProb M (learner ((List.ofFn histT).take t.val)) τ *
            Ylist ((List.ofFn histT).take t.val) τ) := Finset.sum_le_sum (fun t _ => hterm t)
        _ = lsum (fun l _ => ∑ τ, trajProb M (learner l) τ * Ylist l τ) (List.ofFn histT) :=
            (lsum_ofFn_prefix (fun l => ∑ τ, trajProb M (learner l) τ * Ylist l τ) histT).symm
        _ = _ := by
            rw [← lsum_add]
            congr 1
            funext l τ
            ring
    let g : ℕ → ℝ := fun n => if n = 0 then 1 else
      min 1 (bonus δ (Fintype.card S) (Fintype.card A) H T n + beta n)
    have hg : ∀ n, g n ≤ phiP cc (n + 1) - phiP cc n := by
      intro n
      apply phi_step cc hcc0 n (g n)
      · simp only [g]
        split_ifs
        · exact le_rfl
        · exact min_le_left _ _
      · intro hn
        simp only [g, if_neg hn]
        refine le_trans (min_le_right _ _) (le_of_eq ?_)
        unfold bonus
        rw [← hL1def, hccdef]
        show 2 * Real.sqrt (L1 / n) + Real.sqrt (ℓ2 / (2 * n)) = _
        rw [Real.sqrt_div' L1 (Nat.cast_nonneg n),
          show ℓ2 / (2 * (n : ℝ)) = ℓ2 / 2 / n by ring, Real.sqrt_div' _ (Nat.cast_nonneg n)]
        ring
    have hYsum : lsum Ylist (List.ofFn histT) ≤
        H * ((Fintype.card S * Fintype.card A : ℝ) +
          2 * cc * Real.sqrt ((Fintype.card S * Fintype.card A : ℝ) * T)) := by
      have e := lsum_finsum (Finset.range H)
        (fun h l τ => xi δ T beta l h (stateAt τ h) (actionAt τ h)) (List.ofFn histT)
      calc lsum Ylist (List.ofFn histT)
          = ∑ h ∈ Finset.range H,
              lsum (fun l τ => xi δ T beta l h (stateAt τ h) (actionAt τ h)) (List.ofFn histT) := e
        _ ≤ ∑ h ∈ Finset.range H, ((Fintype.card S * Fintype.card A : ℝ) +
              2 * cc * Real.sqrt ((Fintype.card S * Fintype.card A : ℝ) * T)) := by
            apply Finset.sum_le_sum
            intro h _
            have h1 := pigeon_layer cc h g hg (List.ofFn histT)
            have h2 := phi_total cc hcc0 h (List.ofFn histT)
            rw [List.length_ofFn] at h2
            exact le_trans h1 h2
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hRHSdef, show Real.log ((Fintype.card S : ℝ) * Fintype.card A * H * T / δ) = L0 by
      rw [hL0def, hNdef]]
    have hℓ2le : ℓ2 ≤ 5 * Fintype.card S * L0 := by
      rw [hℓ2eq]
      have h1 : (Fintype.card S : ℝ) * Real.log 2 ≤ Fintype.card S * L0 :=
        mul_le_mul_of_nonneg_left hL0 (by positivity)
      have h2 : L0 ≤ (Fintype.card S : ℝ) * L0 := le_mul_of_one_le_left hL0n hS1
      linarith only [h1, h2, hlog6, hL0]
    have hcb : cc ≤ 5 * Real.sqrt (Fintype.card S) * Real.sqrt L0 := by
      rw [hccdef]
      exact c_bound L0 L1 ℓ2 _ hL0n hS1 (by rw [hL1eq]; linarith only [hL0]) hℓ2le
    have hzb := z_bound (T : ℝ) L0 ℓ3 (Nat.cast_nonneg _) hL0n hℓ3le
    have hq : 4 / 5 ≤ Real.sqrt L0 := by
      rw [show (4 / 5 : ℝ) = Real.sqrt ((4 / 5) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num; linarith only [hL0, hlog2])
    have hsq : Real.sqrt ((Fintype.card S * Fintype.card A : ℝ) * T) =
        Real.sqrt (Fintype.card S) * Real.sqrt (Fintype.card A * T) := by
      rw [mul_assoc, Real.sqrt_mul (by positivity)]
    rw [hsq] at hYsum
    have hr2 : FoundationsRL.TabularRL.regret M learner T histT ≤
        H * ((Fintype.card S : ℝ) * Fintype.card A + 2 * cc * (Real.sqrt (Fintype.card S) *
          Real.sqrt (Fintype.card A * T))) + H * Real.sqrt (T * ℓ3 / 2) := by
      linarith only [hregX, hYsum, hn3]
    exact final_numeric H (Fintype.card S) (Fintype.card A) T (Real.sqrt L0) cc
      (Real.sqrt (Fintype.card S)) (Real.sqrt (Fintype.card A * T)) (Real.sqrt T)
      (Real.sqrt (T * ℓ3 / 2)) _ hH1 hS1 hA1 hT1 hq (Real.sqrt_nonneg _)
      (Real.sq_sqrt (by positivity)) (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity))
      (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity)) hcc0 hcb hzb hregT hr2
  rw [probEvent_compl M learner hL T E]
  linarith only [hbad]

end Main

end UCBVIFR

open FoundationsRL.RLBasics FoundationsRL.TabularRL in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {S A : Type u} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (T : ℕ) (δ : ℝ) (learner : Learner S A H),
        0 < δ →
        (∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1) →
        (∀ h, h < H → ∀ s, 0 ≤ Vstar M h s ∧ Vstar M h s ≤ 1) →
        IsUCBVI M M.R δ T learner →
        1 - δ ≤ probEvent M learner T (fun histT =>
          regret M learner T histT ≤
            C * H * Fintype.card S * Real.sqrt (Fintype.card A * T) *
              Real.sqrt (Real.log (Fintype.card S * Fintype.card A * H * T / δ))) := by
  exact ⟨30, by norm_num, fun M T δ learner hδ hR hV1 hU =>
    UCBVIFR.main_fixed M T δ learner hδ hR hV1 hU⟩
