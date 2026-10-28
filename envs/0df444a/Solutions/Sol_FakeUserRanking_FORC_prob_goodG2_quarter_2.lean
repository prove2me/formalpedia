-- Prove2me | solution 2 for FakeUserRanking.FORC.prob_goodG2_quarter
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:29:52.280019+00:00
-- url     : https://prove2.me/submissions/ffcf9807-83b7-456a-aee7-3b74e327486d

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

set_option autoImplicit false

open FakeUserRanking.FORC

namespace L5QuarterAux

variable {n L T : ℕ}

lemma reach_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    0 ≤ reach inst π j := by
  unfold reach
  apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro r _
  · linarith [(inst.q_mem r).2]
  · linarith [(inst.μ_mem (π r)).2]

lemma realW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (o : Obs n) :
    0 ≤ realW inst π o := by
  rcases o with ⟨j, b⟩
  have h1 := reach_nonneg inst π j
  have h2 := (inst.μ_mem (π j)).1
  have h3 := (inst.μ_mem (π j)).2
  have h4 := (inst.q_mem j).1
  cases b
  · simp only [realW]
    apply mul_nonneg (mul_nonneg h1 (by linarith))
    split_ifs <;> linarith
  · simp only [realW]; exact mul_nonneg h1 h2

noncomputable def rho (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) : ℝ :=
  if h : m < n then reach inst π ⟨m, h⟩ else 0

lemma reach_succ (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) (h : m + 1 < n) :
    reach inst π ⟨m + 1, h⟩ = reach inst π ⟨m, by omega⟩ *
      ((1 - inst.q ⟨m, by omega⟩) * (1 - inst.μ (π ⟨m, by omega⟩))) := by
  unfold reach
  have hI : Finset.Iio (⟨m + 1, h⟩ : Fin n) = insert ⟨m, by omega⟩ (Finset.Iio ⟨m, by omega⟩) := by
    ext r; simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]; omega
  rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  ring

lemma reach_zero (inst : Instance n) (π : Equiv.Perm (Fin n)) (h : 0 < n) :
    reach inst π ⟨0, h⟩ = 1 := by
  unfold reach
  have hI : Finset.Iio (⟨0, h⟩ : Fin n) = ∅ := by
    ext r; simp [Fin.lt_def]
  simp [hI]

lemma realW_pair (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    realW inst π (j, true) + realW inst π (j, false) = rho inst π j - rho inst π (j + 1) := by
  simp only [realW, rho, dif_pos j.isLt]
  by_cases h : (j : ℕ) + 1 < n
  · rw [dif_pos h, if_pos h, reach_succ inst π j h]
    ring
  · rw [dif_neg h, if_neg h]; ring

lemma realW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (hn : 1 ≤ n) :
    ∑ o, realW inst π o = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp only [realW_pair]
  rw [Fin.sum_univ_eq_sum_range (fun m => rho inst π m - rho inst π (m + 1)) n]
  rw [Finset.sum_range_sub']
  simp [rho, dif_pos (show 0 < n by omega), reach_zero inst π (show 0 < n by omega)]

def DepBelow (m : ℕ) {β : Type*} (f : (Fin T → Step n L) → β) : Prop :=
  ∀ τ τ' : Fin T → Step n L, (∀ i : Fin T, (i : ℕ) < m → τ i = τ' i) → f τ = f τ'

lemma DepBelow.mono {m m' : ℕ} {β : Type*} {f : (Fin T → Step n L) → β} (h : DepBelow m f)
    (hm : m ≤ m') : DepBelow m' f :=
  fun τ τ' hτ => h τ τ' (fun i hi => hτ i (lt_of_lt_of_le hi hm))

lemma algHist_dep (s : ℕ) : DepBelow (T := T) (n := n) (L := L) s (fun τ => algHist τ s) := by
  intro τ τ' h
  beta_reduce
  unfold algHist
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h
    simp at h1; simp; omega

lemma ranking_dep (A : Alg n L) (s : Fin T) :
    DepBelow (s + 1) (fun τ => ranking A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold ranking
  have e := algHist_dep (n := n) (L := L) s τ τ' (fun i hi => h i (by omega))
  beta_reduce at e
  rw [e, h s (by omega)]

lemma pubHist_dep (A : Alg n L) (s : ℕ) : DepBelow (T := T) s (fun τ => pubHist A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold pubHist
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp at h1
    have e := ranking_dep A ⟨i, by omega⟩ τ τ' (fun j hj => h j (by simp at hj; omega))
    beta_reduce at e
    rw [e, h ⟨i, by omega⟩ (by simp; omega)]

lemma stepW_dep (inst : Instance n) (P : Adversary n) (A : Alg n L) (s : Fin T) :
    DepBelow (s + 1) (fun τ => stepW inst P A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold stepW
  have e1 := algHist_dep (n := n) (L := L) s τ τ' (fun i hi => h i (by omega))
  have e2 := pubHist_dep A s τ τ' (fun i hi => h i (by omega))
  have e3 := ranking_dep A s τ τ' h
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3, h s (by omega)]

lemma update_agree (τ : Fin T → Step n L) (m : Fin T) (x : Step n L) :
    ∀ i : Fin T, (i : ℕ) < m → Function.update τ m x i = τ i := by
  intro i hi
  exact Function.update_of_ne (by intro h; rw [h] at hi; exact lt_irrefl _ hi) _ _

noncomputable def Wm (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : ℕ)
    (τ : Fin T → Step n L) : ℝ :=
  ∏ s : Fin T, if (s : ℕ) < m then stepW inst P A τ s else (Fintype.card (Step n L) : ℝ)⁻¹

noncomputable def Em (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : ℕ)
    (g : (Fin T → Step n L) → ℝ) : ℝ :=
  ∑ τ, Wm inst P A m τ * g τ

lemma sum_update_eq {α : Type*} [Fintype α] [DecidableEq α] (F : (Fin T → α) → ℝ) (m : Fin T) :
    ∑ τ, ∑ x, F (Function.update τ m x) = (Fintype.card α : ℝ) * ∑ τ, F τ := by
  let Φ : (Fin T → α) × α → (Fin T → α) × α := fun p => (Function.update p.1 m p.2, p.1 m)
  have hΦ : Function.Involutive Φ := by
    intro p; simp [Φ]
  calc ∑ τ, ∑ x, F (Function.update τ m x) = ∑ p : (Fin T → α) × α, F (Φ p).1 := by
        rw [Fintype.sum_prod_type]
    _ = ∑ p : (Fin T → α) × α, F p.1 :=
        Fintype.sum_equiv (hΦ.toPerm Φ) _ _ (fun p => rfl)
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp [Finset.sum_const, Finset.mul_sum]

lemma Wm_update (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (τ : Fin T → Step n L) (x : Step n L) (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Wm inst P A (m + 1) (Function.update τ m x) =
      (Fintype.card (Step n L) : ℝ) * Wm inst P A m τ * stepW inst P A (Function.update τ m x) m := by
  unfold Wm
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m),
    ← Finset.mul_prod_erase Finset.univ (fun s : Fin T => if (s : ℕ) < m then stepW inst P A τ s
      else (Fintype.card (Step n L) : ℝ)⁻¹) (Finset.mem_univ m)]
  simp only [lt_add_iff_pos_right, lt_irrefl, if_false, Nat.lt_succ_self, if_true]
  have hrest : ∏ s ∈ Finset.univ.erase m, (if (s : ℕ) < (m : ℕ) + 1 then
      stepW inst P A (Function.update τ m x) s else (Fintype.card (Step n L) : ℝ)⁻¹) =
      ∏ s ∈ Finset.univ.erase m, (if (s : ℕ) < m then stepW inst P A τ s
        else (Fintype.card (Step n L) : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro s hs
    have hsm : s ≠ m := Finset.ne_of_mem_erase hs
    have hsm' : (s : ℕ) ≠ m := fun h => hsm (Fin.ext h)
    by_cases hlt : (s : ℕ) < m
    · rw [if_pos (by omega), if_pos hlt]
      have e := stepW_dep inst P A s _ _ (fun i hi => update_agree τ m x i (by omega))
      beta_reduce at e
      exact e
    · rw [if_neg (by omega), if_neg hlt]
  rw [hrest]
  field_simp

lemma Em_step (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (g : (Fin T → Step n L) → ℝ) (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Em inst P A (m + 1) g = Em inst P A m (fun τ => ∑ x, stepW inst P A (Function.update τ m x) m *
      g (Function.update τ m x)) := by
  unfold Em
  have := sum_update_eq (fun τ => Wm inst P A (m + 1) τ * g τ) m
  have e : ∑ τ, Wm inst P A (m + 1) τ * g τ =
      (Fintype.card (Step n L) : ℝ)⁻¹ * ∑ τ, ∑ x, Wm inst P A (m + 1) (Function.update τ m x) *
        g (Function.update τ m x) := by
    rw [this]; field_simp
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Wm_update inst P A m τ x hN]
  field_simp

lemma stepW_update (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (τ : Fin T → Step n L) (x : Step n L) :
    stepW inst P A (Function.update τ m x) m = A.w (algHist τ m) x.1 *
      (P (pubHist A τ m) x.2.1).toReal * obsW inst (A.rank (algHist τ m) x.1) x.2.1 x.2.2 := by
  unfold stepW ranking
  have e1 := algHist_dep (n := n) (L := L) m _ τ (update_agree τ m x)
  have e2 := pubHist_dep A m _ τ (update_agree τ m x)
  beta_reduce at e1 e2
  rw [Function.update_self, e1, e2]

lemma obsW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (hn : 1 ≤ n) :
    ∑ o, obsW inst π a o = 1 := by
  cases a with
  | none => exact realW_sum inst π hn
  | some a => simp [obsW]

lemma obsW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (o : Obs n) :
    0 ≤ obsW inst π a o := by
  cases a with
  | none => exact realW_nonneg inst π o
  | some a => simp only [obsW]; split_ifs <;> norm_num

lemma pmf_sum (p : PMF (Action n)) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)]
  rw [← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe]; simp

lemma stepW_sum (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (m : Fin T) (τ : Fin T → Step n L) :
    ∑ x, stepW inst P A (Function.update τ m x) m = 1 := by
  simp only [stepW_update]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans (hw_sum (algHist τ m))
  rw [Fintype.sum_prod_type]
  simp only
  simp only [mul_assoc, ← Finset.mul_sum, obsW_sum inst _ _ hn, mul_one]
  rw [pmf_sum, mul_one]

lemma stepW_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (τ : Fin T → Step n L) (s : Fin T) :
    0 ≤ stepW inst P A τ s := by
  unfold stepW
  exact mul_nonneg (mul_nonneg (hw_nonneg _ _) ENNReal.toReal_nonneg) (obsW_nonneg _ _ _ _)

lemma Wm_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (m : ℕ) (τ : Fin T → Step n L) : 0 ≤ Wm inst P A m τ := by
  unfold Wm
  apply Finset.prod_nonneg
  intro s _
  split_ifs
  · exact stepW_nonneg inst P A hw_nonneg τ s
  · positivity

lemma Em_drop (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : Fin T) (g : (Fin T → Step n L) → ℝ) (hg : DepBelow m g) :
    Em inst P A (m + 1) g = Em inst P A m g := by
  rw [Em_step inst P A m g hN]
  congr 1
  funext τ
  have : ∀ x, g (Function.update τ m x) = g τ := fun x => hg _ _ (update_agree τ m x)
  simp only [this, ← Finset.sum_mul, stepW_sum inst P A hw_sum hn m τ, one_mul]

lemma expect_eq_Em (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : ℕ) (hm : m ≤ T) (g : (Fin T → Step n L) → ℝ) (hg : DepBelow m g) :
    expect inst P A T g = Em inst P A m g := by
  have hT : expect inst P A T g = Em inst P A T g := by
    unfold expect Em trajW Wm
    apply Finset.sum_congr rfl
    intro τ _
    congr 1
    apply Finset.prod_congr rfl
    intro s _
    rw [if_pos s.isLt]
  rw [hT]
  have key : ∀ d, m + d ≤ T → Em inst P A (m + d) g = Em inst P A m g := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have := Em_drop inst P A hw_sum hn hN ⟨m + d, by omega⟩ g (hg.mono (by simp))
      simp only at this
      rw [← add_assoc, this, ih (by omega)]
  have := key (T - m) (by omega)
  rwa [show m + (T - m) = T by omega] at this

lemma Em_zero_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Em inst P A (T := T) 0 (fun _ => 1) = 1 := by
  unfold Em Wm
  simp only [Nat.not_lt_zero, if_false, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul, Fintype.card_fun, Nat.cast_pow]
  rw [← mul_pow, mul_inv_cancel₀ hN.ne', one_pow]

lemma Em_mono (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (m : ℕ) (f g : (Fin T → Step n L) → ℝ)
    (hfg : ∀ τ, f τ ≤ g τ) : Em (T := T) inst P A m f ≤ Em (T := T) inst P A m g := by
  unfold Em
  apply Finset.sum_le_sum
  intro τ _
  exact mul_le_mul_of_nonneg_left (hfg τ) (Wm_nonneg inst P A hw_nonneg m τ)

lemma pubHist_succ (A : Alg n L) (τ : Fin T → Step n L) (t : ℕ) (ht : t < T) :
    pubHist A τ (t + 1) = pubHist A τ t ++
      [(ranking A τ ⟨t, ht⟩, (τ ⟨t, ht⟩).2.1.isSome, (τ ⟨t, ht⟩).2.2)] := by
  unfold pubHist
  rw [List.take_add_one]
  simp [ht]

lemma budget_path (inst : Instance n) (P : Adversary n) (A : Alg n L) (F : ℕ)
    (hP : WithinBudget F P) (τ : Fin T → Step n L) (hτ : ∀ s, stepW inst P A τ s ≠ 0) :
    ∀ s, s ≤ T → ((pubHist A τ s).filter (fun s => s.2.1)).length ≤ F ∧
      (((pubHist A τ s).filter (fun s => s.2.1)).length : ℝ) =
        ∑ t ∈ Finset.range s, (if h : t < T then (if (τ ⟨t, h⟩).2.1.isSome then 1 else 0) else 0) := by
  intro s
  induction s with
  | zero => intro _; simp [pubHist]
  | succ s ih =>
    intro hs
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [pubHist_succ A τ s (by omega), List.filter_append, List.length_append,
      Finset.sum_range_succ, dif_pos (show s < T by omega), ← ih2]
    have hstep := hτ ⟨s, by omega⟩
    by_cases hF : F ≤ ((pubHist A τ s).filter (fun s => s.2.1)).length
    · have hPn := hP _ hF
      have hnone : (τ ⟨s, by omega⟩).2.1 = none := by
        by_contra hc
        apply hstep
        unfold stepW
        rw [hPn, PMF.pure_apply, if_neg hc]
        simp
      simp [hnone]
      omega
    · constructor
      · cases h : (τ ⟨s, by omega⟩).2.1.isSome <;> simp [h] <;> omega
      · cases h : (τ ⟨s, by omega⟩).2.1.isSome <;> simp [h]

noncomputable def fac (k : Fin L) (c : ℝ) (x : Step n L) : ℝ :=
  Real.exp ((if x.2.1.isSome then 1 else 0) * ((if x.1 = k then 1 else 0) - c))

noncomputable def Mt (k : Fin L) (c : ℝ) (t : ℕ) (τ : Fin T → Step n L) : ℝ :=
  ∏ s : Fin T, if (s : ℕ) < t then fac k c (τ s) else 1

lemma Mt_update (k : Fin L) (c : ℝ) (m : Fin T) (τ : Fin T → Step n L) (x : Step n L) :
    Mt k c (m + 1) (Function.update τ m x) = Mt k c m τ * fac k c x := by
  unfold Mt
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m),
    ← Finset.mul_prod_erase Finset.univ (fun s : Fin T => if (s : ℕ) < m then fac k c (τ s)
      else 1) (Finset.mem_univ m)]
  simp only [lt_irrefl, if_false, Nat.lt_succ_self, if_true, Function.update_self, one_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  have hsm : s ≠ m := Finset.ne_of_mem_erase hs
  have hsm' : (s : ℕ) ≠ m := fun h => hsm (Fin.ext h)
  by_cases hlt : (s : ℕ) < m
  · rw [if_pos (by omega), if_pos hlt, Function.update_of_ne hsm]
  · rw [if_neg (by omega), if_neg hlt]

lemma Mt_dep (k : Fin L) (c : ℝ) (t : ℕ) : DepBelow (T := T) (n := n) t (Mt k c t) := by
  intro τ τ' h
  unfold Mt
  apply Finset.prod_congr rfl
  intro s _
  split_ifs with hs
  · rw [h s hs]
  · rfl

lemma Mt_nonneg (k : Fin L) (c : ℝ) (t : ℕ) (τ : Fin T → Step n L) : 0 ≤ Mt k c t τ := by
  unfold Mt
  apply Finset.prod_nonneg
  intro s _
  split_ifs
  · exact (Real.exp_pos _).le
  · norm_num

lemma fac_sum (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (k : Fin L) (p : ℝ) (hwk : ∀ h, A.w h k ≤ p)
    (m : Fin T) (τ : Fin T → Step n L) :
    ∑ x, stepW inst P A (Function.update τ m x) m * fac k ((Real.exp 1 - 1) * p) x ≤ 1 := by
  simp only [stepW_update]
  set h := algHist τ m
  set q := P (pubHist A τ m)
  have e1 : ∑ x : Step n L, A.w h x.1 * (q x.2.1).toReal * obsW inst (A.rank h x.1) x.2.1 x.2.2 *
      fac k ((Real.exp 1 - 1) * p) x =
      ∑ a : Action n, (q a).toReal * ∑ l : Fin L, A.w h l * fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true)) := by
    rw [Fintype.sum_prod_type]
    calc _ = ∑ l : Fin L, ∑ a : Action n, (q a).toReal *
          (A.w h l * fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true))) := by
          apply Finset.sum_congr rfl; intro l _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro a _
          dsimp only
          have : ∀ o : Obs n, fac k ((Real.exp 1 - 1) * p) (l, a, o) =
              fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true)) := fun o => rfl
          simp only [this]
          rw [← Finset.sum_mul, ← Finset.mul_sum, obsW_sum inst _ _ hn]; ring
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  rw [e1]
  have hinner : ∀ a : Action n, ∑ l : Fin L, A.w h l * fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true)) ≤ 1 := by
    intro a
    cases a with
    | none => simp [fac, hw_sum]
    | some a =>
      simp only [fac, Option.isSome_some, if_true, one_mul]
      have hsplit : ∀ l : Fin L, A.w h l * Real.exp ((if l = k then 1 else 0) - (Real.exp 1 - 1) * p) =
          Real.exp (-((Real.exp 1 - 1) * p)) * (A.w h l + (if l = k then A.w h l * (Real.exp 1 - 1) else 0)) := by
        intro l
        split_ifs
        · rw [show (1 : ℝ) - (Real.exp 1 - 1) * p = 1 + -((Real.exp 1 - 1) * p) by ring, Real.exp_add]; ring
        · simp only [zero_sub, add_zero]; ring
      simp only [hsplit]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hw_sum, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hb : 1 + A.w h k * (Real.exp 1 - 1) ≤ Real.exp ((Real.exp 1 - 1) * p) := by
        have := Real.add_one_le_exp ((Real.exp 1 - 1) * p)
        have := mul_le_mul_of_nonneg_right (hwk h) he1
        nlinarith
      calc Real.exp (-((Real.exp 1 - 1) * p)) * (1 + A.w h k * (Real.exp 1 - 1))
          ≤ Real.exp (-((Real.exp 1 - 1) * p)) * Real.exp ((Real.exp 1 - 1) * p) :=
            mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
  calc ∑ a : Action n, (q a).toReal * ∑ l : Fin L, A.w h l * fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true))
      ≤ ∑ a : Action n, (q a).toReal * 1 :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hinner a) ENNReal.toReal_nonneg)
    _ = 1 := by simp only [mul_one]; exact pmf_sum q

lemma E_Mt_le (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (hN : (0 : ℝ) < Fintype.card (Step n L))
    (k : Fin L) (p : ℝ) (hwk : ∀ h, A.w h k ≤ p) :
    ∀ t, t ≤ T → expect inst P A T (Mt k ((Real.exp 1 - 1) * p) t) ≤ 1 := by
  intro t
  induction t with
  | zero =>
    intro _
    have : Mt (T := T) (n := n) k ((Real.exp 1 - 1) * p) 0 = fun _ => 1 := by
      funext τ; simp [Mt]
    rw [this, expect_eq_Em inst P A hw_sum hn hN 0 (Nat.zero_le _) _ (fun _ _ _ => rfl),
      Em_zero_one inst P A hN]
  | succ t ih =>
    intro ht
    rw [expect_eq_Em inst P A hw_sum hn hN (t + 1) ht _ (Mt_dep k _ (t + 1))]
    have := Em_step inst P A (⟨t, by omega⟩ : Fin T) (Mt k ((Real.exp 1 - 1) * p) (t + 1)) hN
    rw [this]
    calc _ ≤ Em (T := T) inst P A t (Mt k ((Real.exp 1 - 1) * p) t) := by
          apply Em_mono inst P A hw_nonneg
          intro τ
          have hu : ∀ x, Mt k ((Real.exp 1 - 1) * p) (t + 1) (Function.update τ (⟨t, by omega⟩ : Fin T) x) =
              Mt k ((Real.exp 1 - 1) * p) t τ * fac k ((Real.exp 1 - 1) * p) x :=
            fun x => Mt_update k _ (⟨t, by omega⟩ : Fin T) τ x
          simp only [hu]
          have hs := fac_sum inst P A hw_nonneg hw_sum hn k p hwk (⟨t, by omega⟩ : Fin T) τ
          have hM := Mt_nonneg k ((Real.exp 1 - 1) * p) t τ
          calc ∑ x, stepW inst P A (Function.update τ ⟨t, by omega⟩ x) ⟨t, by omega⟩ *
                (Mt k ((Real.exp 1 - 1) * p) t τ * fac k ((Real.exp 1 - 1) * p) x)
              = Mt k ((Real.exp 1 - 1) * p) t τ * ∑ x, stepW inst P A (Function.update τ ⟨t, by omega⟩ x) ⟨t, by omega⟩ *
                fac k ((Real.exp 1 - 1) * p) x := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
            _ ≤ Mt k ((Real.exp 1 - 1) * p) t τ * 1 := mul_le_mul_of_nonneg_left hs hM
            _ = _ := mul_one _
      _ = expect inst P A T (Mt k ((Real.exp 1 - 1) * p) t) :=
          (expect_eq_Em inst P A hw_sum hn hN t (by omega) _ (Mt_dep k _ t)).symm
      _ ≤ 1 := ih (by omega)

lemma exposure_real (k : Fin L) (τ : Fin T → Step n L) :
    (exposure k τ : ℝ) = ∑ s : Fin T, (if (τ s).2.1.isSome then 1 else 0) * (if (τ s).1 = k then 1 else 0) := by
  unfold exposure
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  by_cases h1 : (τ s).1 = k <;> by_cases h2 : (τ s).2.1.isSome <;> simp [h1, h2]

lemma Mt_T (k : Fin L) (c : ℝ) (τ : Fin T → Step n L) :
    Mt k c T τ = Real.exp ((exposure k τ : ℝ) - c * ∑ s : Fin T, (if (τ s).2.1.isSome then 1 else 0)) := by
  unfold Mt
  simp only [Fin.is_lt, if_true]
  rw [exposure_real, Finset.mul_sum, ← Finset.sum_sub_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro s _
  unfold fac
  congr 1
  ring

lemma fake_count_le (inst : Instance n) (P : Adversary n) (A : Alg n L) (F : ℕ)
    (hP : WithinBudget F P) (τ : Fin T → Step n L) (hτ : ∀ s, stepW inst P A τ s ≠ 0) :
    ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) ≤ F := by
  obtain ⟨b1, b2⟩ := budget_path inst P A F hP τ hτ T le_rfl
  have : ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) =
      ∑ t ∈ Finset.range T, (if h : t < T then (if (τ ⟨t, h⟩).2.1.isSome then 1 else 0) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => if h : t < T then
      (if (τ ⟨t, h⟩).2.1.isSome then (1 : ℝ) else 0) else 0) T]
    apply Finset.sum_congr rfl
    intro s _
    rw [dif_pos s.isLt]
  rw [this, ← b2]
  exact_mod_cast b1

lemma exposure_le_fake (k : Fin L) (τ : Fin T → Step n L) :
    (exposure k τ : ℝ) ≤ ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) := by
  rw [exposure_real]
  apply Finset.sum_le_sum
  intro s _
  split_ifs <;> norm_num

lemma prob_compl (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (E : (Fin T → Step n L) → Prop) :
    prob inst P A T E = 1 - prob inst P A T (fun τ => ¬ E τ) := by
  have hE1 : expect inst P A T (fun _ => 1) = 1 := by
    rw [expect_eq_Em inst P A hw_sum hn hN 0 (Nat.zero_le _) _ (fun _ _ _ => rfl),
      Em_zero_one inst P A hN]
  rw [← hE1]
  unfold prob expect
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro τ _
  by_cases h : E τ <;> simp [h]

lemma tail_bound (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) (F : ℕ) (hP : WithinBudget F P)
    (k : Fin L) (p : ℝ) (hp0 : 0 ≤ p) (hwk : ∀ h, A.w h k ≤ p) (hFp : (F : ℝ) * p ≤ 1) (a : ℝ) :
    prob inst P A T (fun τ => ¬ (exposure k τ : ℝ) ≤ a) ≤ Real.exp (Real.exp 1 - 1 - a) := by
  set c := (Real.exp 1 - 1) * p with hc
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hc0 : 0 ≤ c := mul_nonneg he1 hp0
  have hcF : c * F ≤ Real.exp 1 - 1 := by
    rw [hc]; nlinarith
  have hM := E_Mt_le inst P A hw_nonneg hw_sum hn hN k p hwk T le_rfl
  calc prob inst P A T (fun τ => ¬ (exposure k τ : ℝ) ≤ a)
      ≤ expect inst P A T (fun τ => Real.exp (c * F - a) * Mt k c T τ) := by
        unfold prob expect
        apply Finset.sum_le_sum
        intro τ _
        by_cases h0 : trajW inst P A T τ = 0
        · rw [h0]; simp
        have hτ : ∀ s, stepW inst P A τ s ≠ 0 := by
          intro s hs; apply h0; unfold trajW
          exact Finset.prod_eq_zero (Finset.mem_univ s) hs
        have hW : 0 ≤ trajW inst P A T τ :=
          Finset.prod_nonneg (fun s _ => stepW_nonneg inst P A hw_nonneg τ s)
        apply mul_le_mul_of_nonneg_left _ hW
        have hY := fake_count_le inst P A F hP τ hτ
        beta_reduce
        by_cases hx : (exposure k τ : ℝ) ≤ a
        · simp only [hx, not_true_eq_false, if_false]
          exact mul_nonneg (Real.exp_pos _).le (Mt_nonneg k c T τ)
        · simp only [hx, not_false_eq_true, if_true]
          push_neg at hx
          rw [Mt_T, ← Real.exp_add]
          apply Real.one_le_exp
          have := mul_le_mul_of_nonneg_left hY hc0
          linarith
    _ = Real.exp (c * F - a) * expect inst P A T (Mt k c T) := by
        unfold expect; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro τ _; ring
    _ ≤ Real.exp (c * F - a) * 1 := mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ ≤ Real.exp (Real.exp 1 - 1 - a) := by
        rw [mul_one]; apply Real.exp_le_exp.mpr; linarith

lemma pathwise_bound (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) (F : ℕ) (hP : WithinBudget F P)
    (k : Fin L) (a : ℝ) (hFa : (F : ℝ) ≤ a) :
    prob inst P A T (fun τ => ¬ (exposure k τ : ℝ) ≤ a) = 0 := by
  unfold prob expect
  apply Finset.sum_eq_zero
  intro τ _
  by_cases h0 : trajW inst P A T τ = 0
  · rw [h0]; simp
  have hτ : ∀ s, stepW inst P A τ s ≠ 0 := by
    intro s hs; apply h0; unfold trajW
    exact Finset.prod_eq_zero (Finset.mem_univ s) hs
  have h1 := fake_count_le inst P A F hP τ hτ
  have h2 := exposure_le_fake k τ
  beta_reduce
  rw [if_neg (by push_neg; linarith)]
  simp

lemma S_eq (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) =
    ∑ i ∈ Finset.range (L - 1), (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ i := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + i + 1 = i + 2 by ring, pow_add]
  norm_num
  ring

lemma S_le (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) ≤ 1 / 2 := by
  rw [S_eq, ← Finset.mul_sum]
  have := sum_geometric_two_le (L - 1)
  linarith

lemma levelW_nonneg (L : ℕ) (k : Fin L) : 0 ≤ levelW L k := by
  unfold levelW
  split_ifs
  · linarith [S_le L]
  · positivity

lemma levelW_sum (L : ℕ) (hL : 1 ≤ L) : ∑ k : Fin L, levelW L k = 1 := by
  unfold levelW
  rw [Fin.sum_univ_eq_sum_range (fun m => if m = 0 then 1 - ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1)
    else (1 / 2 : ℝ) ^ (m + 1)) L]
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, if_false, if_true]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have : ∀ i ∈ Finset.range L', (1 / 2 : ℝ) ^ (1 + i + 1) = (1 / 2 : ℝ) ^ (i + 1 + 1) := by
    intro i _; rw [show 1 + i + 1 = i + 1 + 1 by ring]
  rw [Finset.sum_congr rfl this]
  ring

lemma core_bound_quarter (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    prob inst P (forc n T tb fb) T
        (fun τ => ¬ (exposure k τ : ℝ) ≤ Real.log (2 * (numLevels T : ℝ) / δ) + 3)
      ≤ δ / (4 * (numLevels T : ℝ)) := by
  set A := forc n T tb fb
  have hL : 0 < numLevels T := Fin.pos k
  have hL' : (1 : ℝ) ≤ numLevels T := by exact_mod_cast hL
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun _ k => levelW_nonneg _ k
  have hw_sum : ∀ h, ∑ k, A.w h k = 1 := fun _ => levelW_sum _ hL
  have hN : (0 : ℝ) < Fintype.card (Step n (numLevels T)) := by
    have : Nonempty (Step n (numLevels T)) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  have hx : 1 < 2 * (numLevels T : ℝ) / δ := by
    rw [lt_div_iff₀ hδ0]; linarith
  have hlog : 0 ≤ Real.log (2 * (numLevels T : ℝ) / δ) := Real.log_nonneg hx.le
  have hpos : 0 ≤ δ / (4 * (numLevels T : ℝ)) := by positivity
  by_cases hk0 : (k : ℕ) = 0
  · rw [pathwise_bound inst P A hw_nonneg hw_sum hn hN F hP k _ ?_]
    · exact hpos
    · rw [hk0] at hk
      have : (F : ℝ) ≤ 2 := by exact_mod_cast hk
      linarith
  · have hwk : ∀ h, A.w h k ≤ (1 / 2 : ℝ) ^ ((k : ℕ) + 1) := by
      intro _
      show levelW _ k ≤ _
      unfold levelW; rw [if_neg hk0]
    have hFp : (F : ℝ) * (1 / 2 : ℝ) ^ ((k : ℕ) + 1) ≤ 1 := by
      have : (F : ℝ) ≤ 2 ^ ((k : ℕ) + 1) := by exact_mod_cast hk
      rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
      exact this
    refine le_trans (tail_bound inst P A hw_nonneg hw_sum hn hN F hP k _ (by positivity) hwk hFp _) ?_
    have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hinv2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos 1) (by norm_num)]
      exact he2
    have hlog_eq : Real.exp (-Real.log (2 * (numLevels T : ℝ) / δ)) = δ / (2 * (numLevels T : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by linarith)]
      field_simp
    calc Real.exp (Real.exp 1 - 1 - (Real.log (2 * (numLevels T : ℝ) / δ) + 3))
        ≤ Real.exp (-1 + -Real.log (2 * (numLevels T : ℝ) / δ)) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = Real.exp (-1) * Real.exp (-Real.log (2 * (numLevels T : ℝ) / δ)) := Real.exp_add _ _
      _ = Real.exp (-1) * (δ / (2 * (numLevels T : ℝ))) := by rw [hlog_eq]
      _ ≤ (1 / 2) * (δ / (2 * (numLevels T : ℝ))) :=
          mul_le_mul_of_nonneg_right hinv2 (by positivity)
      _ = δ / (4 * (numLevels T : ℝ)) := by ring

end L5QuarterAux

lemma union_pt_q {ι : Type*} [Fintype ι] (E : Prop) (Ek : ι → Prop) {hE : Decidable E}
    {hk : ∀ k, Decidable (Ek k)} (h : E → ∃ k, Ek k) :
    (if E then (1 : ℝ) else 0) ≤ ∑ k, if Ek k then (1 : ℝ) else 0 := by
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), (0 : ℝ) ≤ if Ek j then (1 : ℝ) else 0 := by
    intro j _; split_ifs <;> norm_num
  by_cases hE' : E
  · rw [if_pos hE']
    obtain ⟨k, hk'⟩ := h hE'
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ k))
    rw [if_pos hk']
  · rw [if_neg hE']
    exact Finset.sum_nonneg hnn

open Classical L5QuarterAux in
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)) :
    1 - delta n T / 4 ≤ prob inst P (forc n T tb fb) T (goodG2 F) := by
  unfold goodG2
  set A := forc n T tb fb
  set δ := delta n T with hδ
  have hL : 0 < numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hL' : (0 : ℝ) < numLevels T := by exact_mod_cast hL
  have hN : (0 : ℝ) < Fintype.card (Step n (numLevels T)) := by
    have : Nonempty (Step n (numLevels T)) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hδ0 : 0 < δ := by rw [hδ]; unfold delta; positivity
  have hδ1 : δ < 1 := by
    rw [hδ]; unfold delta
    have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn'
    rw [div_lt_one (by positivity)]
    nlinarith
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun _ k => levelW_nonneg _ k
  set a := Real.log (2 * (numLevels T : ℝ) / δ) + 3
  have hk_bound : ∀ k : Fin (numLevels T),
      prob inst P A T (fun τ => F ≤ 2 ^ ((k : ℕ) + 1) ∧ ¬ (exposure k τ : ℝ) ≤ a) ≤
        δ / (4 * (numLevels T : ℝ)) := by
    intro k
    by_cases hk : F ≤ 2 ^ ((k : ℕ) + 1)
    · have e : (fun τ : Fin T → Step n (numLevels T) => F ≤ 2 ^ ((k : ℕ) + 1) ∧ ¬ (exposure k τ : ℝ) ≤ a) =
          fun τ => ¬ (exposure k τ : ℝ) ≤ a := by
        funext τ; simp [hk]
      rw [e]
      exact core_bound_quarter n T F hn hT inst P hP tb fb δ hδ0 hδ1 k hk
    · have : prob inst P A T (fun τ => F ≤ 2 ^ ((k : ℕ) + 1) ∧ ¬ (exposure k τ : ℝ) ≤ a) = 0 := by
        unfold prob expect; simp [hk]
      rw [this]; positivity
  have hunion : prob inst P A T (fun τ => ¬ ∀ k : Fin (numLevels T), F ≤ 2 ^ ((k : ℕ) + 1) →
      (exposure k τ : ℝ) ≤ a) ≤
      ∑ k : Fin (numLevels T), prob inst P A T (fun τ => F ≤ 2 ^ ((k : ℕ) + 1) ∧ ¬ (exposure k τ : ℝ) ≤ a) := by
    unfold prob expect
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro τ _
    rw [← Finset.mul_sum]
    have hW : 0 ≤ trajW inst P A T τ :=
      Finset.prod_nonneg (fun s _ => stepW_nonneg inst P A hw_nonneg τ s)
    apply mul_le_mul_of_nonneg_left _ hW
    refine union_pt_q (E := ¬ ∀ k : Fin (numLevels T), F ≤ 2 ^ ((k : ℕ) + 1) → (exposure k τ : ℝ) ≤ a)
      (Ek := fun (k : Fin (numLevels T)) => F ≤ 2 ^ ((k : ℕ) + 1) ∧ ¬ (exposure k τ : ℝ) ≤ a) ?_
    intro hE
    push_neg at hE
    obtain ⟨k, hk, hlt⟩ := hE
    exact ⟨k, hk, not_le.mpr hlt⟩
  rw [prob_compl inst P A (fun _ => levelW_sum _ hL) hn hN]
  have hsum : ∑ k : Fin (numLevels T), prob inst P A T
      (fun τ => F ≤ 2 ^ ((k : ℕ) + 1) ∧ ¬ (exposure k τ : ℝ) ≤ a) ≤ δ / 4 := by
    calc _ ≤ ∑ _k : Fin (numLevels T), δ / (4 * (numLevels T : ℝ)) := Finset.sum_le_sum (fun k _ => hk_bound k)
      _ = δ / 4 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  linarith
