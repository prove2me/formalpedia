-- Prove2me | solution 1 for FoundationsRL.FuncApprox.confidence_set_validity_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:13:47.463997+00:00
-- url     : https://prove2.me/submissions/03bc32e2-f848-4714-8150-a382eb7970b7

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB
import Definitions.Def_FoundationsRL_FuncApprox_Normalization



namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

section A
variable {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] {H : ℕ}

def kk (M : EpisodicMDP S A H) (π : Policy S A H) (l : ℕ) (s : S) (x : A × S) : ℝ :=
  π l s x.1 * M.P l s x.1 x.2

def stP (s0 : S) {m : ℕ} (p : Fin m → A × S) : ℕ → S
  | 0 => s0
  | l+1 => if hl : l < m then (p ⟨l, hl⟩).2 else s0

noncomputable def wpre (M : EpisodicMDP S A H) (π : Policy S A H) (m : ℕ)
    (q : S × (Fin m → A × S)) : ℝ :=
  M.d1 q.1 * ∏ l : Fin m, kk M π l.1 (stP q.1 q.2 l.1) (q.2 l)

lemma stP_snoc_le (s0 : S) {m : ℕ} (p : Fin m → A × S) (x : A × S) :
    ∀ l ≤ m, stP s0 (Fin.snoc (α := fun _ => A × S) p x : Fin (m+1) → A × S) l = stP s0 p l := by
  intro l hl
  cases l with
  | zero => rfl
  | succ l =>
    have hl' : l < m := by omega
    have : (⟨l, by omega⟩ : Fin (m+1)) = Fin.castSucc ⟨l, hl'⟩ := rfl
    simp only [stP, dif_pos hl', dif_pos (show l < m + 1 by omega), this, Fin.snoc_castSucc]

lemma stP_snoc_last (s0 : S) {m : ℕ} (p : Fin m → A × S) (x : A × S) :
    stP s0 (Fin.snoc (α := fun _ => A × S) p x : Fin (m+1) → A × S) (m+1) = x.2 := by
  have : (⟨m, by omega⟩ : Fin (m+1)) = Fin.last m := rfl
  simp only [stP, dif_pos (show m < m + 1 by omega), this, Fin.snoc_last]

lemma wpre_snoc (M : EpisodicMDP S A H) (π : Policy S A H) {m : ℕ} (s0 : S) (p : Fin m → A × S)
    (x : A × S) :
    wpre M π (m+1) (s0, Fin.snoc (α := fun _ => A × S) p x) =
      wpre M π m (s0, p) * kk M π m (stP s0 p m) x := by
  unfold wpre
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
  rw [mul_assoc]
  congr 2
  · refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [stP_snoc_le s0 p x l.1 l.2.le]
  · rw [stP_snoc_le s0 p x m le_rfl]

lemma sum_pre_succ {m : ℕ} (F : S × (Fin (m+1) → A × S) → ℝ) :
    ∑ q, F q = ∑ q : S × (Fin m → A × S), ∑ x : A × S, F (q.1, Fin.snoc (α := fun _ => A × S) q.2 x) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun s0 _ => ?_)
  rw [Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m+1) => A × S)).symm (fun u => F (s0, u))
    (fun y => F (s0, (Fin.snocEquiv (fun _ : Fin (m+1) => A × S)) y)) (by intro u; simp only [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type_right]
  rfl

lemma kk_sum (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) {l : ℕ} (hl : l < H)
    (s : S) : ∑ x : A × S, kk M π l s x = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [kk, ← Finset.mul_sum, M.P_sum_one, mul_one]
  exact (hπ l hl s).2

lemma stP_trunc (s0 : S) {N m : ℕ} (hmN : m ≤ N) (p : Fin N → A × S) :
    ∀ l ≤ m, stP s0 (fun j : Fin m => p (Fin.castLE hmN j)) l = stP s0 p l := by
  intro l hl
  cases l with
  | zero => rfl
  | succ l =>
    have hl' : l < m := by omega
    simp only [stP, dif_pos hl', dif_pos (show l < N by omega)]
    rfl

lemma tail_sum (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) {m : ℕ}
    (F : S × (Fin m → A × S) → ℝ) :
    ∀ N (hmN : m ≤ N), N ≤ H →
    ∑ q : S × (Fin N → A × S), wpre M π N q * F (q.1, fun j => q.2 (Fin.castLE hmN j)) =
      ∑ q : S × (Fin m → A × S), wpre M π m q * F q := by
  intro N hmN
  induction N, hmN using Nat.le_induction with
  | base =>
    intro _
    rfl
  | succ N hmN ih =>
    intro hNH
    rw [sum_pre_succ]
    have h1 : ∀ (q : S × (Fin N → A × S)) (x : A × S),
        wpre M π (N+1) (q.1, Fin.snoc (α := fun _ => A × S) q.2 x) *
          F (q.1, fun j => (Fin.snoc (α := fun _ => A × S) q.2 x : Fin (N+1) → A × S)
              (Fin.castLE (hmN.trans (Nat.le_succ N)) j)) =
        wpre M π N q * F (q.1, fun j => q.2 (Fin.castLE hmN j)) * kk M π N (stP q.1 q.2 N) x := by
      intro q x
      rw [wpre_snoc]
      have : (fun j : Fin m => (Fin.snoc (α := fun _ => A × S) q.2 x : Fin (N+1) → A × S)
              (Fin.castLE (hmN.trans (Nat.le_succ N)) j)) = fun j => q.2 (Fin.castLE hmN j) := by
        funext j
        have : Fin.castLE (hmN.trans (Nat.le_succ N)) j = Fin.castSucc (Fin.castLE hmN j) := rfl
        rw [this, Fin.snoc_castSucc]
      rw [this]; ring
    have h2 : ∀ q : S × (Fin N → A × S), ∑ x : A × S, wpre M π (N+1) (q.1, Fin.snoc (α := fun _ => A × S) q.2 x) *
          F (q.1, fun j => (Fin.snoc (α := fun _ => A × S) q.2 x : Fin (N+1) → A × S)
              (Fin.castLE (hmN.trans (Nat.le_succ N)) j)) =
        wpre M π N q * F (q.1, fun j => q.2 (Fin.castLE hmN j)) := by
      intro q
      simp only [h1]
      rw [← Finset.mul_sum, kk_sum M π hπ (by omega), mul_one]
    simp only [h2]
    exact ih (by omega)

lemma stateAt_eq_stP (τ : Trajectory S A H) : ∀ l ≤ H, stateAt τ l = stP τ.1 τ.2 l := by
  intro l hl
  cases l with
  | zero => rfl
  | succ l =>
    have hl' : l < H := by omega
    simp only [stateAt, nextStateAt, stP, dif_pos hl']

lemma trajProb_eq_wpre (M : EpisodicMDP S A H) (π : Policy S A H) (τ : Trajectory S A H) :
    trajProb M π τ = wpre M π H τ := by
  unfold trajProb wpre
  congr 1
  refine Finset.prod_congr rfl (fun l _ => ?_)
  have h1 : stateAt τ l.1 = stP τ.1 τ.2 l.1 := stateAt_eq_stP τ l.1 l.2.le
  have h2 : actionAt τ l.1 = (τ.2 l).1 := by simp [actionAt, l.2]
  have h3 : nextStateAt τ l.1 = (τ.2 l).2 := by simp [nextStateAt, l.2]
  simp only [kk, h1, h2, h3]

lemma pre_state_marg (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (φ : S → ℝ) :
    ∑ q : S × (Fin h → A × S), wpre M π h q * φ (stP q.1 q.2 h) =
      ∑ s0 : S, M.d1 s0 * ∑ s : S, stateDist M π s0 h s * φ s := by
  induction h generalizing φ with
  | zero =>
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun s0 _ => ?_)
    simp [wpre, stP, stateDist]
  | succ h ih =>
    rw [sum_pre_succ]
    have h1 : ∀ (q : S × (Fin h → A × S)) (x : A × S),
        wpre M π (h+1) (q.1, Fin.snoc (α := fun _ => A × S) q.2 x) *
          φ (stP q.1 (Fin.snoc (α := fun _ => A × S) q.2 x : Fin (h+1) → A × S) (h+1)) =
        wpre M π h q * (kk M π h (stP q.1 q.2 h) x * φ x.2) := by
      intro q x
      rw [wpre_snoc, stP_snoc_last]; ring
    simp only [h1, ← Finset.mul_sum]
    rw [ih (fun s => ∑ x : A × S, kk M π h s x * φ x.2)]
    refine Finset.sum_congr rfl (fun s0 _ => ?_)
    congr 1
    simp only [stateDist, kk, Finset.sum_mul, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun sp _ => ?_)
    simp only [Finset.mul_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma traj_marg (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) {h : ℕ} (hh : h < H)
    (g : S → A → S → ℝ) :
    ∑ τ : Trajectory S A H, trajProb M π τ * g (stateAt τ h) (actionAt τ h) (nextStateAt τ h) =
      ∑ s0 : S, M.d1 s0 * ∑ s : S, stateDist M π s0 h s *
        ∑ a : A, π h s a * ∑ s' : S, M.P h s a s' * g s a s' := by
  set F : S × (Fin (h+1) → A × S) → ℝ := fun q =>
    g (stP q.1 q.2 h) (q.2 (Fin.last h)).1 (q.2 (Fin.last h)).2 with hF
  have key := tail_sum M π hπ F H (by omega) le_rfl
  have e1 : ∀ τ : Trajectory S A H, trajProb M π τ * g (stateAt τ h) (actionAt τ h) (nextStateAt τ h)
      = wpre M π H τ * F (τ.1, fun j => τ.2 (Fin.castLE (by omega) j)) := by
    intro τ
    rw [trajProb_eq_wpre]
    congr 1
    have h1 : stateAt τ h = stP τ.1 τ.2 h := stateAt_eq_stP τ h hh.le
    have h2 : actionAt τ h = (τ.2 ⟨h, hh⟩).1 := by simp [actionAt, hh]
    have h3 : nextStateAt τ h = (τ.2 ⟨h, hh⟩).2 := by simp [nextStateAt, hh]
    have h4 : stP τ.1 (fun j : Fin (h+1) => τ.2 (Fin.castLE (by omega) j)) h = stP τ.1 τ.2 h :=
      stP_trunc τ.1 (by omega) τ.2 h (Nat.le_succ h)
    simp only [hF, h1, h2, h3, h4]
    rfl
  simp only [e1]
  rw [key, sum_pre_succ]
  have e2 : ∀ (q : S × (Fin h → A × S)) (x : A × S),
      wpre M π (h+1) (q.1, Fin.snoc (α := fun _ => A × S) q.2 x) *
        F (q.1, (Fin.snoc (α := fun _ => A × S) q.2 x : Fin (h+1) → A × S)) =
      wpre M π h q * (kk M π h (stP q.1 q.2 h) x * g (stP q.1 q.2 h) x.1 x.2) := by
    intro q x
    rw [wpre_snoc]
    simp only [hF, Fin.snoc_last, stP_snoc_le q.1 q.2 x h le_rfl]
    ring
  simp only [e2, ← Finset.mul_sum]
  rw [pre_state_marg M π h (fun s => ∑ x : A × S, kk M π h s x * g s x.1 x.2)]
  refine Finset.sum_congr rfl (fun s0 _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun s _ => ?_)
  congr 1
  simp only [kk, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  ring

lemma traj_sum_one (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    ∑ τ : Trajectory S A H, trajProb M π τ = 1 := by
  have key := tail_sum M π hπ (m := 0) (fun _ => (1:ℝ)) H (Nat.zero_le _) le_rfl
  simp only [mul_one] at key
  simp only [trajProb_eq_wpre]
  rw [key]
  rw [Fintype.sum_prod_type]
  simp [wpre, M.d1_sum_one]

lemma trajProb_nonneg (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π)
    (τ : Trajectory S A H) : 0 ≤ trajProb M π τ := by
  unfold trajProb
  refine mul_nonneg (M.d1_nonneg _) (Finset.prod_nonneg (fun l _ => ?_))
  exact mul_nonneg ((hπ l.1 l.2 _).1 _) (M.P_nonneg _ _ _ _)

end A

open MeasureTheory ProbabilityTheory in
theorem hoeffding_fin {X : Type} [Fintype X] (w : X → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (z : X → ℝ) (a b : ℝ) (hz : ∀ x, z x ∈ Set.Icc a b) (θ : ℝ) :
    ∑ x, w x * Real.exp (θ * (z x - ∑ y, w y * z y)) ≤ Real.exp ((b - a) ^ 2 / 8 * θ ^ 2) := by
  classical
  let ν : Measure ℝ := ∑ x, ENNReal.ofReal (w x) • Measure.dirac (z x)
  have hintg : ∀ f : ℝ → ℝ, Integrable f ν := by
    intro f
    exact integrable_finsetSum_measure.2 (fun x _ =>
      (integrable_dirac (by simp)).smul_measure (by simp))
  have hint : ∀ f : ℝ → ℝ, ∫ y, f y ∂ν = ∑ x, w x * f (z x) := by
    intro f
    simp only [ν]
    rw [integral_finsetSum_measure (fun x _ => (integrable_dirac (by simp)).smul_measure (by simp))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [integral_smul_measure, integral_dirac]
    simp [ENNReal.toReal_ofReal (hw0 x)]
  have : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _)]
    simp only [smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hw0 x), hw1]
    simp
  have hmean : ν[id] = ∑ y, w y * z y := by
    have := hint id
    simpa using this
  have hae : ∀ᵐ y ∂ν, y ∈ Set.Icc a b := by
    rw [ae_iff]
    have hm : MeasurableSet {y : ℝ | ¬ y ∈ Set.Icc a b} := (measurableSet_Icc).compl
    simp only [ν, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [Measure.dirac_apply' _ hm,
      Set.indicator_of_notMem (show z x ∉ {y : ℝ | ¬ y ∈ Set.Icc a b} from fun h => h (hz x))]
    simp
  have hsg := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := id) aemeasurable_id hae
  have hm := hsg.mgf_le θ
  rw [mgf, hmean] at hm
  simp only [id] at hm
  rw [hint (fun y => Real.exp (θ * (y - ∑ y, w y * z y)))] at hm
  have hc : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) = (b-a)^2 / 4 := by
    push_cast
    rw [Real.norm_eq_abs, div_pow, sq_abs]; norm_num
  rw [hc] at hm
  convert hm using 2
  ring


section B
variable {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] {H : ℕ}

lemma ofFn_snoc_take {m : ℕ} (h : Fin m → Trajectory S A H) (τ : Trajectory S A H) (t : ℕ)
    (ht : t ≤ m) :
    (List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)).take t
      = (List.ofFn h).take t := by
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  rw [List.take_append_of_le_length (by simpa using ht)]

lemma ofFn_snoc_full {m : ℕ} (h : Fin m → Trajectory S A H) (τ : Trajectory S A H) :
    (List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)).take m
      = List.ofFn h := by
  rw [ofFn_snoc_take h τ m le_rfl]
  simp

lemma hist_snoc (M : EpisodicMDP S A H) (L : Learner S A H) {m : ℕ}
    (h : Fin m → Trajectory S A H) (τ : Trajectory S A H) :
    historyProb M L (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)
      = historyProb M L h * trajProb M (L (List.ofFn h)) τ := by
  unfold historyProb
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [ofFn_snoc_take h τ t.1 t.2.le]
  · rw [ofFn_snoc_full]

lemma sum_hist_succ (M : EpisodicMDP S A H) (L : Learner S A H) {m : ℕ}
    (F : (Fin (m+1) → Trajectory S A H) → ℝ) :
    ∑ h, historyProb M L h * F h =
      ∑ h : Fin m → Trajectory S A H, historyProb M L h *
        ∑ τ : Trajectory S A H, trajProb M (L (List.ofFn h)) τ *
          F (Fin.snoc (α := fun _ => Trajectory S A H) h τ) := by
  rw [Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m+1) => Trajectory S A H)).symm
    (fun u => historyProb M L u * F u)
    (fun y => historyProb M L ((Fin.snocEquiv (fun _ : Fin (m+1) => Trajectory S A H)) y) *
       F ((Fin.snocEquiv (fun _ : Fin (m+1) => Trajectory S A H)) y))
    (by intro u; simp only [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  have : (Fin.snocEquiv (fun _ : Fin (m+1) => Trajectory S A H)) (τ, h) =
      Fin.snoc (α := fun _ => Trajectory S A H) h τ := rfl
  rw [this, hist_snoc]
  ring

lemma hist_nonneg (M : EpisodicMDP S A H) (L : Learner S A H) (hL : ∀ l, IsPolicy H (L l)) {m : ℕ}
    (h : Fin m → Trajectory S A H) : 0 ≤ historyProb M L h :=
  Finset.prod_nonneg (fun t _ => trajProb_nonneg M _ (hL _) _)

lemma hist_sum_one (M : EpisodicMDP S A H) (L : Learner S A H) (hL : ∀ l, IsPolicy H (L l)) :
    ∀ m : ℕ, ∑ h : Fin m → Trajectory S A H, historyProb M L h = 1 := by
  intro m
  induction m with
  | zero => simp [historyProb]
  | succ m ih =>
    have := sum_hist_succ M L (m := m) (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    simp only [traj_sum_one M _ (hL _), mul_one]
    exact ih

end B

section C
variable {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] {H : ℕ}

noncomputable def tmean (M : EpisodicMDP S A H) (π : Policy S A H) (z : Trajectory S A H → ℝ) : ℝ :=
  ∑ τ, trajProb M π τ * z τ

theorem exp_super (M : EpisodicMDP S A H) (L : Learner S A H) (hL : ∀ l, IsPolicy H (L l))
    (z : Trajectory S A H → ℝ) (a b : ℝ) (hz : ∀ τ, z τ ∈ Set.Icc a b)
    (θ : ℕ → List (Trajectory S A H) → ℝ) :
    ∀ m : ℕ, ∑ h : Fin m → Trajectory S A H, historyProb M L h *
      Real.exp (∑ t : Fin m, (θ t.1 ((List.ofFn h).take t.1) *
          (z (h t) - tmean M (L ((List.ofFn h).take t.1)) z) -
        (b - a) ^ 2 / 8 * (θ t.1 ((List.ofFn h).take t.1)) ^ 2)) ≤ 1 := by
  intro m
  induction m with
  | zero => simp [historyProb]
  | succ m ih =>
    rw [sum_hist_succ]
    have step : ∀ h : Fin m → Trajectory S A H, 
        ∑ τ : Trajectory S A H, trajProb M (L (List.ofFn h)) τ *
          Real.exp (∑ t : Fin (m+1), (θ t.1 ((List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)).take t.1) *
          (z ((Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H) t) - tmean M (L ((List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)).take t.1)) z) -
        (b - a) ^ 2 / 8 * (θ t.1 ((List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)).take t.1)) ^ 2))
        ≤ Real.exp (∑ t : Fin m, (θ t.1 ((List.ofFn h).take t.1) *
          (z (h t) - tmean M (L ((List.ofFn h).take t.1)) z) -
        (b - a) ^ 2 / 8 * (θ t.1 ((List.ofFn h).take t.1)) ^ 2)) := by
      intro h
      have e1 : ∀ τ : Trajectory S A H, 
          Real.exp (∑ t : Fin (m+1), (θ t.1 ((List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)).take t.1) *
          (z ((Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H) t) - tmean M (L ((List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)).take t.1)) z) -
        (b - a) ^ 2 / 8 * (θ t.1 ((List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)).take t.1)) ^ 2))
          = Real.exp (∑ t : Fin m, (θ t.1 ((List.ofFn h).take t.1) *
          (z (h t) - tmean M (L ((List.ofFn h).take t.1)) z) -
        (b - a) ^ 2 / 8 * (θ t.1 ((List.ofFn h).take t.1)) ^ 2)) *
          (Real.exp (θ m (List.ofFn h) * (z τ - tmean M (L (List.ofFn h)) z)) *
            Real.exp (-((b - a) ^ 2 / 8 * (θ m (List.ofFn h)) ^ 2))) := by
        intro τ
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
        rw [ofFn_snoc_full]
        have : ∀ t : Fin m, (List.ofFn (Fin.snoc (α := fun _ => Trajectory S A H) h τ : Fin (m+1) → Trajectory S A H)).take t.1 = (List.ofFn h).take t.1 :=
          fun t => ofFn_snoc_take h τ t.1 t.2.le
        simp only [this]
        have hsub : ∀ X Y : ℝ, Real.exp (X - Y) = Real.exp X * Real.exp (-Y) := by
          intro X Y; rw [sub_eq_add_neg, Real.exp_add]
        rw [Real.exp_add, hsub]
      simp only [e1]
      have : ∑ τ : Trajectory S A H, trajProb M (L (List.ofFn h)) τ *
          (Real.exp (∑ t : Fin m, (θ t.1 ((List.ofFn h).take t.1) *
          (z (h t) - tmean M (L ((List.ofFn h).take t.1)) z) -
        (b - a) ^ 2 / 8 * (θ t.1 ((List.ofFn h).take t.1)) ^ 2)) *
          (Real.exp (θ m (List.ofFn h) * (z τ - tmean M (L (List.ofFn h)) z)) *
            Real.exp (-((b - a) ^ 2 / 8 * (θ m (List.ofFn h)) ^ 2)))) =
        Real.exp (∑ t : Fin m, (θ t.1 ((List.ofFn h).take t.1) *
          (z (h t) - tmean M (L ((List.ofFn h).take t.1)) z) -
        (b - a) ^ 2 / 8 * (θ t.1 ((List.ofFn h).take t.1)) ^ 2)) *
          (Real.exp (-((b - a) ^ 2 / 8 * (θ m (List.ofFn h)) ^ 2)) *
            ∑ τ : Trajectory S A H, trajProb M (L (List.ofFn h)) τ *
              Real.exp (θ m (List.ofFn h) * (z τ - tmean M (L (List.ofFn h)) z))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        ring
      rw [this]
      have hh := hoeffding_fin (fun τ => trajProb M (L (List.ofFn h)) τ)
        (fun τ => trajProb_nonneg M _ (hL _) τ) (traj_sum_one M _ (hL _)) z a b hz (θ m (List.ofFn h))
      have hh' : Real.exp (-((b - a) ^ 2 / 8 * (θ m (List.ofFn h)) ^ 2)) *
            ∑ τ : Trajectory S A H, trajProb M (L (List.ofFn h)) τ *
              Real.exp (θ m (List.ofFn h) * (z τ - tmean M (L (List.ofFn h)) z)) ≤ 1 := by
        calc _ ≤ Real.exp (-((b - a) ^ 2 / 8 * (θ m (List.ofFn h)) ^ 2)) *
              Real.exp ((b - a) ^ 2 / 8 * (θ m (List.ofFn h)) ^ 2) :=
              mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; simp
      calc _ ≤ Real.exp (∑ t : Fin m, (θ t.1 ((List.ofFn h).take t.1) *
          (z (h t) - tmean M (L ((List.ofFn h).take t.1)) z) -
        (b - a) ^ 2 / 8 * (θ t.1 ((List.ofFn h).take t.1)) ^ 2)) * 1 :=
            mul_le_mul_of_nonneg_left hh' (Real.exp_pos _).le
        _ = _ := mul_one _
    calc _ ≤ ∑ h : Fin m → Trajectory S A H, historyProb M L h * 
        Real.exp (∑ t : Fin m, (θ t.1 ((List.ofFn h).take t.1) *
          (z (h t) - tmean M (L ((List.ofFn h).take t.1)) z) -
        (b - a) ^ 2 / 8 * (θ t.1 ((List.ofFn h).take t.1)) ^ 2)) :=
          Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (step h) (hist_nonneg M L hL h))
      _ ≤ 1 := ih

end C


section BO

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma bo_V_succ (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (hh : h < H) (s : S) :
    V M π h s = ∑ a, π h s a * (M.R h s a + ∑ s', M.P h s a s' * V M π (h + 1) s') := by
  unfold V
  obtain ⟨k, hk⟩ : ∃ k, H - h = k + 1 := ⟨H - h - 1, by omega⟩
  have h1 : H - 1 - k = h := by omega
  have h2 : H - (h + 1) = k := by omega
  rw [hk, h2]
  simp only [valueAux, h1]

lemma bo_V_top (M : EpisodicMDP S A H) (π : Policy S A H) (s : S) : V M π H s = 0 := by
  simp [V, valueAux]

lemma bo_Q (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (hh : h < H) (s : S) (a : A) :
    Q M π h s a = M.R h s a + ∑ s', M.P h s a s' * V M π (h + 1) s' := by
  simp [Q, hh]

lemma bo_det_valid (πdet : ℕ → S → A) : IsPolicy H (detPolicy (H := H) πdet) := by
  intro h _ s
  refine ⟨fun a => ?_, ?_⟩
  · simp only [detPolicy]; split_ifs <;> norm_num
  · simp [detPolicy]

lemma bo_V_det (M : EpisodicMDP S A H) (πdet : ℕ → S → A) (h : ℕ) (hh : h < H) (s : S) :
    V M (detPolicy πdet) h s = M.R h s (πdet h s)
      + ∑ s', M.P h s (πdet h s) s' * V M (detPolicy πdet) (h + 1) s' := by
  rw [bo_V_succ M _ h hh s]
  simp [detPolicy, ite_mul]

theorem bo_main (M : EpisodicMDP S A H) :
    ∃ πdet : ℕ → S → A,
      (∀ h, h < H → ∀ s : S, IsArgmax (Qstar M h s) (πdet h s)) ∧
      (∀ h, h < H → ∀ s : S, ∀ a : A, Qstar M h s a = bellmanOp M h (Qstar M (h + 1)) s a) ∧
      (∀ h, h ≤ H → ∀ s : S, V M (detPolicy πdet) h s = Vstar M h s) := by
  have hex : ∀ h s, ∃ a, ∀ a', Qstar M h s a' ≤ Qstar M h s a := fun h s => Finite.exists_max _
  choose πdet hπdet using hex
  have hvalid : IsPolicy H (detPolicy (H := H) πdet) := bo_det_valid πdet
  haveI : Nonempty {π : Policy S A H // IsPolicy H π} := ⟨⟨_, hvalid⟩⟩
  have hQtop : ∀ s a, Qstar M H s a = 0 := by
    intro s a
    unfold Qstar
    simp only [Q, lt_irrefl, if_false]
    exact ciSup_const
  have hVstar_max : ∀ h s, Vstar M h s = Qstar M h s (πdet h s) := by
    intro h s
    unfold Vstar
    exact le_antisymm (ciSup_le (hπdet h s)) (le_ciSup (Set.finite_range _).bddAbove _)
  -- one step of backward induction for `Qstar`
  have hQgen : ∀ h, h < H → (∀ s, V M (detPolicy πdet) (h + 1) s = Vstar M (h + 1) s) →
      (∀ π : Policy S A H, IsPolicy H π → ∀ s, V M π (h + 1) s ≤ Vstar M (h + 1) s) →
      ∀ s a, Qstar M h s a = M.R h s a + ∑ s', M.P h s a s' * Vstar M (h + 1) s' := by
    intro h hlt ihdet ihall s a
    have hbound : ∀ π : Policy S A H, IsPolicy H π →
        Q M π h s a ≤ M.R h s a + ∑ s', M.P h s a s' * Vstar M (h + 1) s' := by
      intro π hπ
      rw [bo_Q M π h hlt]
      exact add_le_add le_rfl (Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left (ihall π hπ s') (M.P_nonneg _ _ _ _))
    unfold Qstar
    apply le_antisymm
    · exact ciSup_le fun π => hbound π.1 π.2
    · refine le_ciSup_of_le ?_ ⟨_, hvalid⟩ ?_
      · refine ⟨M.R h s a + ∑ s', M.P h s a s' * Vstar M (h + 1) s', ?_⟩
        rintro _ ⟨π, rfl⟩
        exact hbound π.1 π.2
      · rw [bo_Q M _ h hlt]
        simp only [ihdet]
        exact le_rfl
  have key : ∀ k, k ≤ H → (∀ s, V M (detPolicy πdet) (H - k) s = Vstar M (H - k) s) ∧
      (∀ π : Policy S A H, IsPolicy H π → ∀ s, V M π (H - k) s ≤ Vstar M (H - k) s) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hV0 : ∀ s, Vstar M H s = 0 := by
        intro s
        rw [hVstar_max, hQtop]
      simp only [Nat.sub_zero]
      exact ⟨fun s => by rw [bo_V_top, hV0], fun π _ s => by rw [bo_V_top, hV0]⟩
    | succ k ih =>
      intro hk
      obtain ⟨ihdet, ihall⟩ := ih (by omega)
      have hlt : H - (k + 1) < H := by omega
      have hh1 : H - (k + 1) + 1 = H - k := by omega
      rw [← hh1] at ihdet ihall
      have hQ := hQgen (H - (k + 1)) hlt ihdet ihall
      constructor
      · intro s
        rw [bo_V_det M πdet _ hlt s, hVstar_max _ s, hQ s (πdet _ s)]
        simp only [ihdet]
      · intro π hπ s
        rw [bo_V_succ M π _ hlt s]
        obtain ⟨hπnn, hπsum⟩ := hπ _ hlt s
        calc ∑ a, π (H - (k + 1)) s a * (M.R (H - (k + 1)) s a
              + ∑ s', M.P (H - (k + 1)) s a s' * V M π (H - (k + 1) + 1) s')
            ≤ ∑ a, π (H - (k + 1)) s a * Qstar M (H - (k + 1)) s a := by
              refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hπnn a)
              rw [hQ s a]
              exact add_le_add le_rfl (Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (ihall π hπ s') (M.P_nonneg _ _ _ _))
          _ ≤ ∑ a, π (H - (k + 1)) s a * Vstar M (H - (k + 1)) s := by
              refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hπnn a)
              exact le_ciSup (Set.finite_range _).bddAbove a
          _ = Vstar M (H - (k + 1)) s := by rw [← Finset.sum_mul, hπsum, one_mul]
  refine ⟨πdet, fun h _ s => hπdet h s, ?_, ?_⟩
  · intro h hh s a
    obtain ⟨kd, ka⟩ := key (H - (h + 1)) (by omega)
    rw [show H - (H - (h + 1)) = h + 1 by omega] at kd ka
    rw [hQgen h hh kd ka s a]
    rfl
  · intro h hh s
    have := (key (H - h) (by omega)).1 s
    rwa [show H - (H - h) = h by omega] at this


end BO

section D
variable {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] {H : ℕ}
  {Qc : Type} [Fintype Qc] [Nonempty Qc]

noncomputable def zfun (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (Q : Qc) (h : ℕ)
    (τ : Trajectory S A H) : ℝ :=
  qeval Q h (stateAt τ h) (actionAt τ h) - M.R h (stateAt τ h) (actionAt τ h) -
    (if h + 1 < H then ⨆ a' : A, qeval Q (h + 1) (nextStateAt τ h) a' else 0)

lemma zfun_mean (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (Q : Qc) {h : ℕ}
    (hh : h < H) (π : Policy S A H) (hπ : IsPolicy H π) :
    tmean M π (zfun M qeval Q h) = bellmanResidual M π h (qeval Q) := by
  unfold tmean
  have := traj_marg M π hπ hh (fun s a s' => qeval Q h s a - M.R h s a -
    (if h + 1 < H then ⨆ a' : A, qeval Q (h + 1) s' a' else 0))
  unfold zfun
  rw [this]
  unfold bellmanResidual layerStateActionExp
  refine Finset.sum_congr rfl (fun s0 _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun s _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have hP := M.P_sum_one h s a
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP, one_mul]
  ring_nf

lemma zfun_range (M : EpisodicMDP S A H) (hM : RewardsNormalized M) (qeval : Qc → ℕ → S → A → ℝ)
    (hQ : IsNormalizedValueClass H qeval) (Q : Qc) {h : ℕ} (hh : h < H) (τ : Trajectory S A H) :
    zfun M qeval Q h τ ∈ Set.Icc (-2 : ℝ) 1 := by
  unfold zfun
  have h1 := hQ Q h hh (stateAt τ h) (actionAt τ h)
  have h2 := hM.1 h hh (stateAt τ h) (actionAt τ h)
  have h3 : (if h + 1 < H then ⨆ a' : A, qeval Q (h + 1) (nextStateAt τ h) a' else 0) ∈ Set.Icc (0:ℝ) 1 := by
    split_ifs with hh1
    · constructor
      · obtain ⟨a0⟩ := ‹Nonempty A›
        exact le_trans (hQ Q (h+1) hh1 _ a0).1 (le_ciSup (Set.finite_range _).bddAbove a0)
      · exact ciSup_le (fun a' => (hQ Q (h+1) hh1 _ a').2)
    · exact ⟨le_rfl, zero_le_one⟩
  simp only [Set.mem_Icc] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

lemma Qstar_top (M : EpisodicMDP S A H) (s : S) (a : A) : Qstar M H s a = 0 := by
  have hvalid : IsPolicy H (detPolicy (S := S) (H := H) (fun _ _ => Classical.arbitrary A)) := bo_det_valid _
  haveI : Nonempty {π : Policy S A H // IsPolicy H π} := ⟨⟨_, hvalid⟩⟩
  unfold Qstar
  simp only [Q, lt_irrefl, if_false]
  exact ciSup_const

lemma qstar_bellman (M : EpisodicMDP S A H) {h : ℕ} (hh : h < H) (s : S) (a : A) :
    Qstar M h s a = M.R h s a + ∑ s' : S, M.P h s a s' *
      (if h + 1 < H then ⨆ a' : A, Qstar M (h + 1) s' a' else 0) := by
  obtain ⟨πdet, -, hb, -⟩ := bo_main M
  rw [hb h hh s a]
  unfold bellmanOp
  congr 1
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  congr 1
  split_ifs with h1
  · rfl
  · have : h + 1 = H := by omega
    subst this
    simp [Qstar_top]

lemma q0_mean_zero (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
    (hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0) {h : ℕ} (hh : h < H)
    (π : Policy S A H) (hπ : IsPolicy H π) :
    tmean M π (zfun M qeval q0 h) = 0 := by
  rw [zfun_mean M qeval q0 hh π hπ]
  unfold bellmanResidual layerStateActionExp
  refine Finset.sum_eq_zero (fun s0 _ => ?_)
  rw [show (∑ s : S, stateDist M π s0 h s * ∑ a : A, π h s a *
      (qeval q0 h s a - (M.R h s a + ∑ s' : S, M.P h s a s' *
        (if h + 1 < H then ⨆ a' : A, qeval q0 (h + 1) s' a' else 0)))) = 0 from ?_]
  · simp
  refine Finset.sum_eq_zero (fun s _ => ?_)
  rw [show (∑ a : A, π h s a * (qeval q0 h s a - (M.R h s a + ∑ s' : S, M.P h s a s' *
        (if h + 1 < H then ⨆ a' : A, qeval q0 (h + 1) s' a' else 0)))) = 0 from ?_]
  · simp
  refine Finset.sum_eq_zero (fun a _ => ?_)
  have hb := qstar_bellman M hh s a
  have e1 : qeval q0 h s a = Qstar M h s a := by rw [hq0]; simp [hh]
  have e2 : ∀ s' : S, (if h + 1 < H then ⨆ a' : A, qeval q0 (h + 1) s' a' else 0) =
      (if h + 1 < H then ⨆ a' : A, Qstar M (h + 1) s' a' else 0) := by
    intro s'
    split_ifs with h1
    · rw [hq0]; simp [h1]
    · rfl
  simp only [e2, e1]
  rw [← hb]
  simp

end D

section Gauss
open MeasureTheory ProbabilityTheory

lemma gauss_sq_int : ∫ x, Real.exp (3/8 * x ^ 2) ∂(gaussianReal 0 1) = 2 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal, smul_eq_mul]
  have : (fun x : ℝ => (√(2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) * Real.exp (3 / 8 * x ^ 2))
      = fun x => (√(2 * Real.pi))⁻¹ * Real.exp (-(1/8) * x ^ 2) := by
    funext x
    have e1 : (((1 : NNReal) : ℝ)) = 1 := NNReal.coe_one
    rw [e1, mul_one, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [this, integral_const_mul, integral_gaussian]
  have h1 : √(Real.pi / (1/8)) = 2 * √(2 * Real.pi) := by
    rw [show Real.pi / (1/8) = 2 ^ 2 * (2 * Real.pi) by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h1]
  have : √(2 * Real.pi) ≠ 0 := by positivity
  field_simp

lemma gauss_sq_integrable : Integrable (fun x : ℝ => Real.exp (3/8 * x ^ 2)) (gaussianReal 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [gauss_sq_int]; norm_num

lemma gauss_lin_int (y : ℝ) : ∫ x, Real.exp (x * y) ∂(gaussianReal 0 1) = Real.exp (y ^ 2 / 2) := by
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) y
  simp only [mgf, id] at this
  simpa [mul_comm, Real.exp_zero] using this

lemma gauss_lin_integrable (y : ℝ) : Integrable (fun x : ℝ => Real.exp (x * y)) (gaussianReal 0 1) := by
  simpa [mul_comm] using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) y

theorem gauss_mix {Ω : Type} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) {k : ℕ}
    (y : Ω → Fin k → ℝ)
    (hb : ∀ g : Fin k → ℝ, ∑ ω, w ω * Real.exp (∑ i, g i * y ω i) ≤ Real.exp (3/8 * ∑ i, g i ^ 2)) :
    ∑ ω, w ω * Real.exp (∑ i, y ω i ^ 2 / 2) ≤ 2 ^ k := by
  set γ : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => gaussianReal 0 1) with hγ
  have : IsProbabilityMeasure γ := inferInstance
  have hF : ∀ ω, ∫ g, Real.exp (∑ i, g i * y ω i) ∂γ = Real.exp (∑ i, y ω i ^ 2 / 2) := by
    intro ω
    simp only [Real.exp_sum]
    rw [hγ, integral_fintype_prod_eq_prod (fun i x => Real.exp (x * y ω i))]
    simp only [gauss_lin_int]
  have hFi : ∀ ω, Integrable (fun g : Fin k → ℝ => Real.exp (∑ i, g i * y ω i)) γ := by
    intro ω
    simp only [Real.exp_sum]
    exact Integrable.fintype_prod (fun i => gauss_lin_integrable (y ω i))
  have hGi : Integrable (fun g : Fin k → ℝ => Real.exp (3/8 * ∑ i, g i ^ 2)) γ := by
    have : (fun g : Fin k → ℝ => Real.exp (3/8 * ∑ i, g i ^ 2)) =
        fun g => ∏ i, Real.exp (3/8 * g i ^ 2) := by
      funext g; rw [← Real.exp_sum, Finset.mul_sum]
    rw [this]
    exact Integrable.fintype_prod (fun i => gauss_sq_integrable)
  calc ∑ ω, w ω * Real.exp (∑ i, y ω i ^ 2 / 2)
      = ∑ ω, w ω * ∫ g, Real.exp (∑ i, g i * y ω i) ∂γ := by simp only [hF]
    _ = ∫ g, ∑ ω, w ω * Real.exp (∑ i, g i * y ω i) ∂γ := by
        rw [integral_finsetSum _ (fun ω _ => (hFi ω).const_mul (w ω))]
        simp only [integral_const_mul]
    _ ≤ ∫ g, Real.exp (3/8 * ∑ i, g i ^ 2) ∂γ :=
        integral_mono (integrable_finsetSum _ (fun ω _ => (hFi ω).const_mul (w ω))) hGi hb
    _ = 2 ^ k := by
        have : (fun g : Fin k → ℝ => Real.exp (3/8 * ∑ i, g i ^ 2)) =
            fun g => ∏ i, Real.exp (3/8 * g i ^ 2) := by
          funext g; rw [← Real.exp_sum, Finset.mul_sum]
        rw [this, hγ, integral_fintype_prod_eq_prod (fun i x => Real.exp (3/8 * x ^ 2))]
        simp [gauss_sq_int]

end Gauss

section E
variable {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] {H : ℕ}
  {Qc : Type} [Fintype Qc] [Nonempty Qc]

def bl {K n : ℕ} (histT : Fin (K * n) → Trajectory S A H) (i : Fin K) (j : Fin n) :
    Trajectory S A H := histT (finProdFinEquiv (i, j))

lemma blk_val {K n : ℕ} (i : Fin K) (j : Fin n) :
    (finProdFinEquiv (i, j) : Fin (K * n)).1 = j.1 + n * i.1 := rfl

lemma blk_div {K n : ℕ} (hn : 0 < n) (i : Fin K) (j : Fin n) :
    (finProdFinEquiv (i, j) : Fin (K * n)).1 / n = i.1 := by
  rw [blk_val, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt j.2, zero_add]

lemma sum_blocks {K n : ℕ} (G : Fin (K * n) → ℝ) :
    ∑ t, G t = ∑ i : Fin K, ∑ j : Fin n, G (finProdFinEquiv (i, j)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv finProdFinEquiv _ _ (fun x => rfl)).symm

lemma batch_ofFn {K n : ℕ} (histT : Fin (K * n) → Trajectory S A H) (i : Fin K) :
    batch (List.ofFn histT) n i.1 = List.ofFn (fun j : Fin n => bl histT i j) := by
  apply List.ext_getElem
  · simp only [batch, List.length_take, List.length_drop, List.length_ofFn]
    have : i.1 * n + n ≤ K * n := by
      have := i.2
      nlinarith
    omega
  · intro j h1 h2
    simp only [batch, List.getElem_take, List.getElem_drop, List.getElem_ofFn, bl]
    congr 1
    apply Fin.ext
    simp only [blk_val]
    ring

lemma residualEst_blocks (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) {K n : ℕ}
    (histT : Fin (K * n) → Trajectory S A H) (h : ℕ) (i : Fin K) (Q : Qc) :
    residualEst M qeval (List.ofFn histT) n h i.1 Q =
      (∑ j : Fin n, zfun M qeval Q h (bl histT i j)) / n := by
  unfold residualEst
  rw [batch_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl


lemma L_valid (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (n : ℕ) (β : ℝ)
    (l : List (Trajectory S A H)) : IsPolicy H (biLinUCBLearner M qeval n β l) :=
  bo_det_valid _

lemma iterPolicy_take (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (n : ℕ) (β : ℝ)
    (hist : List (Trajectory S A H)) (i t : ℕ) (ht : i * n ≤ t) :
    iterPolicy M qeval (hist.take t) n β i = iterPolicy M qeval hist n β i := by
  unfold iterPolicy
  rw [List.take_take, Nat.min_eq_left ht]

noncomputable def Eres (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (n : ℕ) (β : ℝ)
    (h : ℕ) (Q : Qc) (i : ℕ) (l : List (Trajectory S A H)) : ℝ :=
  bellmanResidual M (iterPolicy M qeval l n β i) h (qeval Q)

lemma mean_take (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (n : ℕ) (β : ℝ)
    {h : ℕ} (hh : h < H) (Q : Qc) {K : ℕ} (histT : Fin (K * n) → Trajectory S A H)
    (t : Fin (K * n)) :
    tmean M (biLinUCBLearner M qeval n β ((List.ofFn histT).take t.1)) (zfun M qeval Q h)
      = Eres M qeval n β h Q (t.1 / n) (List.ofFn histT) := by
  rw [zfun_mean M qeval Q hh _ (L_valid M qeval n β _)]
  unfold Eres biLinUCBLearner
  have hlen : ((List.ofFn histT).take t.1).length = t.1 := by
    simp only [List.length_take, List.length_ofFn]
    exact Nat.min_eq_left t.2.le
  rw [hlen]
  by_cases hn : n = 0
  · subst hn
    exact absurd t.2 (by simp)
  · rw [iterPolicy_take M qeval n β _ _ _ (Nat.div_mul_le_self t.1 n)]

lemma sum_range_eq_fin {K : ℕ} {k : ℕ} (hk : k ≤ K) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range k, f i = ∑ i : Fin K, if i.1 < k then f i.1 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then f i else 0) K]
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_range, Finset.mem_filter]
  omega


lemma Eres_take (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (n : ℕ) (β : ℝ)
    (h : ℕ) (Q : Qc) (hist : List (Trajectory S A H)) (i t : ℕ) (ht : i * n ≤ t) :
    Eres M qeval n β h Q i (hist.take t) = Eres M qeval n β h Q i hist := by
  unfold Eres
  rw [iterPolicy_take M qeval n β hist i t ht]

lemma part1_exponent (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) {K n : ℕ} (hn : 0 < n)
    (β : ℝ) (k : ℕ) (hk : k ≤ K) {h : ℕ} (hh : h < H) (Q : Qc)
    (histT : Fin (K * n) → Trajectory S A H) :
    (∑ t : Fin (K * n),
      ((fun (t : ℕ) (l : List (Trajectory S A H)) =>
          if t / n < k then -(2 / 9 : ℝ) * Eres M qeval n β h Q (t / n) l else 0) t.1
          ((List.ofFn histT).take t.1) *
        (zfun M qeval Q h (histT t) -
          tmean M (biLinUCBLearner M qeval n β ((List.ofFn histT).take t.1)) (zfun M qeval Q h)) -
        (1 - -2 : ℝ) ^ 2 / 8 *
          ((fun (t : ℕ) (l : List (Trajectory S A H)) =>
            if t / n < k then -(2 / 9 : ℝ) * Eres M qeval n β h Q (t / n) l else 0) t.1
            ((List.ofFn histT).take t.1)) ^ 2)) =
    ∑ i ∈ Finset.range k,
      (-(2 / 9 : ℝ) * Eres M qeval n β h Q i (List.ofFn histT) *
          (n * residualEst M qeval (List.ofFn histT) n h i Q - n * Eres M qeval n β h Q i (List.ofFn histT))
        - (1 / 18 : ℝ) * n * (Eres M qeval n β h Q i (List.ofFn histT)) ^ 2) := by
  rw [sum_blocks, sum_range_eq_fin hk]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hθ : ∀ j : Fin n, 
      (fun (t : ℕ) (l : List (Trajectory S A H)) =>
          if t / n < k then -(2 / 9 : ℝ) * Eres M qeval n β h Q (t / n) l else 0)
        (finProdFinEquiv (i, j) : Fin (K * n)).1
        ((List.ofFn histT).take (finProdFinEquiv (i, j) : Fin (K * n)).1)
      = if i.1 < k then -(2 / 9 : ℝ) * Eres M qeval n β h Q i.1 (List.ofFn histT) else 0 := by
    intro j
    simp only [blk_div hn]
    split_ifs with hik
    · rw [Eres_take M qeval n β h Q _ _ _ (by
        rw [← blk_div hn i j]; exact Nat.div_mul_le_self _ n)]
    · rfl
  have hm : ∀ j : Fin n, tmean M (biLinUCBLearner M qeval n β
      ((List.ofFn histT).take (finProdFinEquiv (i, j) : Fin (K * n)).1)) (zfun M qeval Q h)
      = Eres M qeval n β h Q i.1 (List.ofFn histT) := by
    intro j
    rw [mean_take M qeval n β hh Q histT, blk_div hn]
  simp only [hθ, hm]
  have hres := residualEst_blocks M qeval histT h i Q
  have hsum : ∑ j : Fin n, zfun M qeval Q h (bl histT i j) =
      n * residualEst M qeval (List.ofFn histT) n h i.1 Q := by
    rw [hres]; field_simp
  split_ifs with hik
  · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : ∑ j : Fin n, zfun M qeval Q h (histT (finProdFinEquiv (i, j))) =
        n * residualEst M qeval (List.ofFn histT) n h i.1 Q := hsum
    rw [this]
    ring
  · simp


lemma part1_alg (n : ℝ) (hn : 0 ≤ n) (e Eh : ℕ → ℝ) (k : ℕ) :
    n * ((∑ i ∈ Finset.range k, e i ^ 2) / 18 - (∑ i ∈ Finset.range k, Eh i ^ 2) / 9) ≤
    ∑ i ∈ Finset.range k, (-(2 / 9 : ℝ) * e i * (n * Eh i - n * e i) - (1 / 18 : ℝ) * n * e i ^ 2) := by
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  nlinarith [mul_nonneg hn (sq_nonneg (e i - Eh i))]

theorem part1_prob (M : EpisodicMDP S A H) (hM : RewardsNormalized M)
    (qeval : Qc → ℕ → S → A → ℝ) (hQ : IsNormalizedValueClass H qeval) {K n : ℕ} (hn : 0 < n)
    (β : ℝ) (k : ℕ) (hk : k ≤ K) {h : ℕ} (hh : h < H) (Q : Qc) (δ1 : ℝ) (hδ1 : 0 < δ1)
    (hthr : Real.log (1 / δ1) ≤ n * β / 9) :
    ∑ histT : Fin (K * n) → Trajectory S A H, historyProb M (biLinUCBLearner M qeval n β) histT *
      (if (∑ i ∈ Finset.range k, (residualEst M qeval (List.ofFn histT) n h i Q) ^ 2 ≤ β ∧
        4 * β < ∑ i ∈ Finset.range k, (Eres M qeval n β h Q i (List.ofFn histT)) ^ 2) then 1 else 0)
      ≤ δ1 := by
  have hsuper := exp_super M (biLinUCBLearner M qeval n β) (L_valid M qeval n β)
    (zfun M qeval Q h) (-2) 1 (zfun_range M hM qeval hQ Q hh)
    (fun (t : ℕ) (l : List (Trajectory S A H)) =>
          if t / n < k then -(2 / 9 : ℝ) * Eres M qeval n β h Q (t / n) l else 0) (K * n)
  simp only [part1_exponent M qeval hn β k hk hh Q] at hsuper
  calc _ ≤ ∑ histT : Fin (K * n) → Trajectory S A H, δ1 * (historyProb M (biLinUCBLearner M qeval n β) histT *
      Real.exp (∑ i ∈ Finset.range k,
      (-(2 / 9 : ℝ) * Eres M qeval n β h Q i (List.ofFn histT) *
          (n * residualEst M qeval (List.ofFn histT) n h i Q - n * Eres M qeval n β h Q i (List.ofFn histT))
        - (1 / 18 : ℝ) * n * (Eres M qeval n β h Q i (List.ofFn histT)) ^ 2))) := by
        refine Finset.sum_le_sum (fun histT _ => ?_)
        have hp := hist_nonneg M (biLinUCBLearner M qeval n β) (L_valid M qeval n β) histT
        split_ifs with hc
        · obtain ⟨hB, hA⟩ := hc
          have hX := part1_alg (n : ℝ) (Nat.cast_nonneg n) (fun i => Eres M qeval n β h Q i (List.ofFn histT))
            (fun i => residualEst M qeval (List.ofFn histT) n h i Q) k
          have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
          have h1 : (n : ℝ) * β / 9 ≤ (n : ℝ) * ((∑ i ∈ Finset.range k, Eres M qeval n β h Q i (List.ofFn histT) ^ 2) / 18 -
              (∑ i ∈ Finset.range k, residualEst M qeval (List.ofFn histT) n h i Q ^ 2) / 9) := by
            have : β / 9 ≤ ((∑ i ∈ Finset.range k, Eres M qeval n β h Q i (List.ofFn histT) ^ 2) / 18 -
              (∑ i ∈ Finset.range k, residualEst M qeval (List.ofFn histT) n h i Q ^ 2) / 9) := by
              linarith
            calc (n : ℝ) * β / 9 = n * (β / 9) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left this hnpos.le
          have h2 : Real.log (1 / δ1) ≤ ∑ i ∈ Finset.range k,
      (-(2 / 9 : ℝ) * Eres M qeval n β h Q i (List.ofFn histT) *
          (n * residualEst M qeval (List.ofFn histT) n h i Q - n * Eres M qeval n β h Q i (List.ofFn histT))
        - (1 / 18 : ℝ) * n * (Eres M qeval n β h Q i (List.ofFn histT)) ^ 2) := by
            linarith
          have h3 := Real.exp_le_exp.2 h2
          rw [Real.exp_log (by positivity)] at h3
          have : 1 ≤ δ1 * Real.exp (∑ i ∈ Finset.range k,
      (-(2 / 9 : ℝ) * Eres M qeval n β h Q i (List.ofFn histT) *
          (n * residualEst M qeval (List.ofFn histT) n h i Q - n * Eres M qeval n β h Q i (List.ofFn histT))
        - (1 / 18 : ℝ) * n * (Eres M qeval n β h Q i (List.ofFn histT)) ^ 2)) := by
            rw [one_div] at h3
            calc (1 : ℝ) = δ1 * δ1⁻¹ := by field_simp
              _ ≤ _ := mul_le_mul_of_nonneg_left h3 hδ1.le
          calc historyProb M (biLinUCBLearner M qeval n β) histT * 1
              ≤ historyProb M (biLinUCBLearner M qeval n β) histT * (δ1 * Real.exp (∑ i ∈ Finset.range k,
      (-(2 / 9 : ℝ) * Eres M qeval n β h Q i (List.ofFn histT) *
          (n * residualEst M qeval (List.ofFn histT) n h i Q - n * Eres M qeval n β h Q i (List.ofFn histT))
        - (1 / 18 : ℝ) * n * (Eres M qeval n β h Q i (List.ofFn histT)) ^ 2))) :=
                mul_le_mul_of_nonneg_left this hp
            _ = _ := by ring
        · simp only [mul_zero]
          exact mul_nonneg hδ1.le (mul_nonneg hp (Real.exp_pos _).le)
    _ = δ1 * ∑ histT : Fin (K * n) → Trajectory S A H, (historyProb M (biLinUCBLearner M qeval n β) histT *
      Real.exp (∑ i ∈ Finset.range k,
      (-(2 / 9 : ℝ) * Eres M qeval n β h Q i (List.ofFn histT) *
          (n * residualEst M qeval (List.ofFn histT) n h i Q - n * Eres M qeval n β h Q i (List.ofFn histT))
        - (1 / 18 : ℝ) * n * (Eres M qeval n β h Q i (List.ofFn histT)) ^ 2))) := by
        rw [Finset.mul_sum]
    _ ≤ δ1 * 1 := mul_le_mul_of_nonneg_left hsuper hδ1.le
    _ = δ1 := mul_one _


theorem part2_exponent (M : EpisodicMDP S A H) (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
    (hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
    {K n : ℕ} (hn : 0 < n) (β : ℝ) (k : ℕ) {h : ℕ} (hh : h < H) (t0 : ℝ) (g : Fin K → ℝ)
    (histT : Fin (K * n) → Trajectory S A H) :
    (∑ t : Fin (K * n),
      ((fun (t : ℕ) (l : List (Trajectory S A H)) =>
          if t / n < k then t0 * (if hi : t / n < K then g ⟨t / n, hi⟩ else 0) else 0) t.1
          ((List.ofFn histT).take t.1) *
        (zfun M qeval q0 h (histT t) -
          tmean M (biLinUCBLearner M qeval n β ((List.ofFn histT).take t.1)) (zfun M qeval q0 h)) -
        (1 - -2 : ℝ) ^ 2 / 8 *
          ((fun (t : ℕ) (l : List (Trajectory S A H)) =>
            if t / n < k then t0 * (if hi : t / n < K then g ⟨t / n, hi⟩ else 0) else 0) t.1
            ((List.ofFn histT).take t.1)) ^ 2)) =
    ∑ i : Fin K, (g i * (if i.1 < k then t0 * ∑ j : Fin n, zfun M qeval q0 h (bl histT i j) else 0)
      - 9 / 8 * t0 ^ 2 * n * (if i.1 < k then g i ^ 2 else 0)) := by
  rw [sum_blocks]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hm : ∀ j : Fin n, tmean M (biLinUCBLearner M qeval n β
      ((List.ofFn histT).take (finProdFinEquiv (i, j) : Fin (K * n)).1)) (zfun M qeval q0 h) = 0 :=
    fun j => q0_mean_zero M qeval q0 hq0 hh _ (L_valid M qeval n β _)
  simp only [hm, blk_div hn, dif_pos i.2, Fin.eta, sub_zero]
  split_ifs with hik
  · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : ∀ j : Fin n, bl histT i j = histT (finProdFinEquiv (i, j)) := fun j => rfl
    simp only [← this]
    ring
  · simp

theorem part2_prob (M : EpisodicMDP S A H) (hM : RewardsNormalized M)
    (qeval : Qc → ℕ → S → A → ℝ) (hQ : IsNormalizedValueClass H qeval) (q0 : Qc)
    (hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
    {K n : ℕ} (hn : 0 < n) (β : ℝ) (k : ℕ) (hk : k ≤ K) {h : ℕ} (hh : h < H) :
    ∑ histT : Fin (K * n) → Trajectory S A H, historyProb M (biLinUCBLearner M qeval n β) histT *
      (if β < ∑ i ∈ Finset.range k, (residualEst M qeval (List.ofFn histT) n h i q0) ^ 2
        then 1 else 0) ≤ 2 ^ K * Real.exp (-(n * β / 6)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set L := biLinUCBLearner M qeval n β with hLdef
  set t0 : ℝ := Real.sqrt (1 / (3 * n)) with ht0def
  have ht0 : t0 ^ 2 = 1 / (3 * n) := Real.sq_sqrt (by positivity)
  set y : (Fin (K * n) → Trajectory S A H) → Fin K → ℝ := fun histT i =>
    if i.1 < k then t0 * ∑ j : Fin n, zfun M qeval q0 h (bl histT i j) else 0 with hy
  have hb : ∀ g : Fin K → ℝ, ∑ histT : Fin (K * n) → Trajectory S A H,
      historyProb M L histT * Real.exp (∑ i, g i * y histT i) ≤ Real.exp (3 / 8 * ∑ i, g i ^ 2) := by
    intro g
    have hsuper := exp_super M (biLinUCBLearner M qeval n β) (L_valid M qeval n β) (zfun M qeval q0 h) (-2) 1
      (zfun_range M hM qeval hQ q0 hh)
      (fun (t : ℕ) (l : List (Trajectory S A H)) =>
          if t / n < k then t0 * (if hi : t / n < K then g ⟨t / n, hi⟩ else 0) else 0) (K * n)
    simp only [part2_exponent M qeval q0 hq0 hn β k hh t0 g] at hsuper
    have hc : (9 / 8 : ℝ) * t0 ^ 2 * n = 3 / 8 := by
      rw [ht0]; field_simp; norm_num
    calc ∑ histT : Fin (K * n) → Trajectory S A H, historyProb M L histT * Real.exp (∑ i, g i * y histT i)
        ≤ ∑ histT : Fin (K * n) → Trajectory S A H, Real.exp (3 / 8 * ∑ i, g i ^ 2) *
            (historyProb M L histT * Real.exp (∑ i : Fin K, (g i * y histT i
              - 9 / 8 * t0 ^ 2 * n * (if i.1 < k then g i ^ 2 else 0)))) := by
          refine Finset.sum_le_sum (fun histT _ => ?_)
          have hp := hist_nonneg M L (L_valid M qeval n β) histT
          have : Real.exp (∑ i, g i * y histT i) ≤ Real.exp (3 / 8 * ∑ i, g i ^ 2) *
              Real.exp (∑ i : Fin K, (g i * y histT i
              - 9 / 8 * t0 ^ 2 * n * (if i.1 < k then g i ^ 2 else 0))) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.2
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
            have h1 : ∑ i : Fin K, (if i.1 < k then g i ^ 2 else 0) ≤ ∑ i : Fin K, g i ^ 2 :=
              Finset.sum_le_sum (fun i _ => by split_ifs <;> first | exact le_rfl | exact sq_nonneg _)
            rw [show 9 / 8 * t0 ^ 2 * (n : ℝ) = 3 / 8 from hc]
            nlinarith [h1]
          calc historyProb M L histT * Real.exp (∑ i, g i * y histT i)
              ≤ historyProb M L histT * (Real.exp (3 / 8 * ∑ i, g i ^ 2) *
                Real.exp (∑ i : Fin K, (g i * y histT i
                  - 9 / 8 * t0 ^ 2 * n * (if i.1 < k then g i ^ 2 else 0)))) :=
                mul_le_mul_of_nonneg_left this hp
            _ = _ := by ring
      _ = Real.exp (3 / 8 * ∑ i, g i ^ 2) * ∑ histT : Fin (K * n) → Trajectory S A H,
            (historyProb M L histT * Real.exp (∑ i : Fin K, (g i * y histT i
              - 9 / 8 * t0 ^ 2 * n * (if i.1 < k then g i ^ 2 else 0)))) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ Real.exp (3 / 8 * ∑ i, g i ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hsuper (Real.exp_pos _).le
      _ = _ := mul_one _
  have hmix := gauss_mix (fun histT : Fin (K * n) → Trajectory S A H => historyProb M L histT)
    (fun histT => hist_nonneg M L (L_valid M qeval n β) histT) y hb
  have hB : ∀ histT : Fin (K * n) → Trajectory S A H,
      ∑ i : Fin K, y histT i ^ 2 / 2 =
        n / 6 * ∑ i ∈ Finset.range k, (residualEst M qeval (List.ofFn histT) n h i q0) ^ 2 := by
    intro histT
    rw [sum_range_eq_fin hk]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hy]
    split_ifs with hik
    · rw [residualEst_blocks M qeval histT h i q0]
      have : ∑ j : Fin n, zfun M qeval q0 h (bl histT i j) = 
          n * ((∑ j : Fin n, zfun M qeval q0 h (bl histT i j)) / n) := by field_simp
      rw [mul_pow, ht0]
      field_simp
      ring
    · simp
  simp only [hB] at hmix
  calc _ ≤ ∑ histT : Fin (K * n) → Trajectory S A H, Real.exp (-(n * β / 6)) *
        (historyProb M L histT * Real.exp (n / 6 * ∑ i ∈ Finset.range k,
          (residualEst M qeval (List.ofFn histT) n h i q0) ^ 2)) := by
        refine Finset.sum_le_sum (fun histT _ => ?_)
        have hp := hist_nonneg M L (L_valid M qeval n β) histT
        split_ifs with hc
        · have : 1 ≤ Real.exp (-(n * β / 6)) * Real.exp (n / 6 * ∑ i ∈ Finset.range k,
              (residualEst M qeval (List.ofFn histT) n h i q0) ^ 2) := by
            rw [← Real.exp_add]
            apply Real.one_le_exp
            nlinarith
          calc historyProb M L histT * 1
              ≤ historyProb M L histT * (Real.exp (-(n * β / 6)) * Real.exp (n / 6 * ∑ i ∈ Finset.range k,
              (residualEst M qeval (List.ofFn histT) n h i q0) ^ 2)) :=
                mul_le_mul_of_nonneg_left this hp
            _ = _ := by ring
        · simp only [mul_zero]
          exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hp (Real.exp_pos _).le)
    _ = Real.exp (-(n * β / 6)) * ∑ histT : Fin (K * n) → Trajectory S A H,
        (historyProb M L histT * Real.exp (n / 6 * ∑ i ∈ Finset.range k,
          (residualEst M qeval (List.ofFn histT) n h i q0) ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(n * β / 6)) * 2 ^ K :=
        mul_le_mul_of_nonneg_left hmix (Real.exp_pos _).le
    _ = _ := mul_comm _ _


lemma bounds_real (q : ℝ) (hq : 2 ≤ q) (H K : ℕ) (hH : 1 ≤ H) (hK : 1 ≤ K) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) (nβ : ℝ)
    (hnβ : nβ = 100 * ((K : ℝ) * Real.log q + Real.log ((H : ℝ) * K / δ))) :
    Real.log (1 / (δ / (2 * q * H * K))) ≤ nβ / 9 ∧
    (2 : ℝ) ^ K * Real.exp (-(nβ / 6)) ≤ δ / (2 * K * H) := by
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hHK : (1 : ℝ) ≤ H * K := by nlinarith
  have hl2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ℓ := Real.log q with hℓ
  have hL0 : 0 ≤ Real.log ((H : ℝ) * K / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  set L0 := Real.log ((H : ℝ) * K / δ) with hL0def
  have hq0 : 0 < q := by linarith
  constructor
  · have : 1 / (δ / (2 * q * H * K)) = (2 * q) * ((H : ℝ) * K / δ) := by
      field_simp
    rw [this, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hq0.ne']
    rw [← hL0def, ← hℓ, hnβ]
    nlinarith
  · have h2K : (2 : ℝ) ^ K = Real.exp (K * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hd : δ / (2 * K * H) = Real.exp (-(Real.log (2 * K * H / δ))) := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    rw [h2K, hd, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : Real.log (2 * K * H / δ) = Real.log 2 + L0 := by
      have : 2 * (K : ℝ) * H / δ = 2 * ((H : ℝ) * K / δ) := by ring
      rw [this, Real.log_mul (by norm_num) (by positivity)]
    rw [this, hnβ]
    nlinarith


theorem main_bound (M : EpisodicMDP S A H) (hM : RewardsNormalized M)
    (hQc : 1 < Fintype.card Qc) (qeval : Qc → ℕ → S → A → ℝ)
    (hQ : IsNormalizedValueClass H qeval) (q0 : Qc)
    (hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
    {n K : ℕ} (δ : ℝ) (hn : 0 < n) (hδ : 0 < δ) (β : ℝ)
    (hβ : β = 100 * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n) :
    probEvent M (biLinUCBLearner M qeval n β) (K * n)
        (fun histT =>
          ∀ k, k < K →
            (∀ Qf ∈ confSet M qeval (List.ofFn histT) n β k, ∀ h : Fin H,
                ∑ i ∈ Finset.range k,
                  (bellmanResidual M (iterPolicy M qeval (List.ofFn histT) n β i) h.1
                    (qeval Qf)) ^ 2 ≤ 4 * β) ∧
            q0 ∈ confSet M qeval (List.ofFn histT) n β k)
      ≥ 1 - δ := by
  classical
  set L := biLinUCBLearner M qeval n β with hL
  have hLv : ∀ l, IsPolicy H (L l) := L_valid M qeval n β
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold probEvent
  set E : (Fin (K * n) → Trajectory S A H) → Prop := fun histT =>
          ∀ k, k < K →
            (∀ Qf ∈ confSet M qeval (List.ofFn histT) n β k, ∀ h : Fin H,
                ∑ i ∈ Finset.range k,
                  (bellmanResidual M (iterPolicy M qeval (List.ofFn histT) n β i) h.1
                    (qeval Qf)) ^ 2 ≤ 4 * β) ∧
            q0 ∈ confSet M qeval (List.ofFn histT) n β k with hE
  rw [ge_iff_le]
  by_cases hδ1 : 1 ≤ δ
  · exact le_trans (by linarith : 1 - δ ≤ 0) (Finset.sum_nonneg (fun histT _ => by
        split_ifs
        · exact hist_nonneg M L hLv histT
        · exact le_rfl))
  push_neg at hδ1
  have hone := hist_sum_one M L hLv (K * n)
  suffices hsuff : ∑ histT : Fin (K * n) → Trajectory S A H, (if E histT then 0 else historyProb M L histT) ≤ δ by
    refine (show 1 - δ ≤ 1 - ∑ histT : Fin (K * n) → Trajectory S A H, (if E histT then 0 else historyProb M L histT) by linarith).trans (le_of_eq ?_)
    rw [← hone, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun histT _ => ?_)
    split_ifs <;> ring
  -- the bounds
  set q : ℝ := (Fintype.card Qc : ℝ) with hq
  have hq2 : (2 : ℝ) ≤ q := by
    have : 2 ≤ Fintype.card Qc := hQc
    rw [hq]; exact_mod_cast this
  set b2 : ℝ := δ / (2 * K * H) with hb2
  set δ1 : ℝ := δ / (2 * q * H * K) with hδ1def
  have hnβ : (n : ℝ) * β = 100 * ((K : ℝ) * Real.log q + Real.log ((H : ℝ) * K / δ)) := by
    rw [hβ]; field_simp
  -- pointwise bound by union
  have hpt : ∀ histT : Fin (K * n) → Trajectory S A H,
      (if E histT then 0 else historyProb M L histT) ≤
        ∑ k : Fin K, ∑ h : Fin H, historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0) +
        ∑ k : Fin K, ∑ h : Fin H, ∑ Q : Qc, historyProb M L histT *
          (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0) := by
    intro histT
    have hp := hist_nonneg M L hLv histT
    have hnn1 : 0 ≤ ∑ k : Fin K, ∑ h : Fin H, historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0) :=
      Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun h _ => by
        split_ifs <;> simp [hp]))
    have hnn2 : 0 ≤ ∑ k : Fin K, ∑ h : Fin H, ∑ Q : Qc, historyProb M L histT *
          (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0) :=
      Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun h _ => Finset.sum_nonneg (fun Q _ => by
        split_ifs <;> simp [hp])))
    by_cases hEh : E histT
    · rw [if_pos hEh]; linarith
    · rw [if_neg hEh]
      -- extract a bad event
      have hbad : (∃ (k : Fin K) (h : Fin H), β < ∑ i ∈ Finset.range k.1,
            (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2) ∨
          (∃ (k : Fin K) (h : Fin H) (Q : Qc), ∑ i ∈ Finset.range k.1,
            (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2) := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨hc1, hc2⟩ := hcon
        apply hEh
        intro k hk
        constructor
        · intro Qf hQf h
          have hmem := (Finset.mem_filter.1 hQf).2 h
          have := hc2 ⟨k, hk⟩ h Qf hmem
          exact this
        · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h => ?_⟩
          exact hc1 ⟨k, hk⟩ h
      rcases hbad with ⟨k, h, hb⟩ | ⟨k, h, Q, hb⟩
      · have h1 : historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0) ≤ ∑ h : Fin H, historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0) :=
          Finset.single_le_sum (f := fun h : Fin H => historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0)) (fun h _ => by split_ifs <;> simp [hp]) (Finset.mem_univ h)
        have h2 : ∑ h : Fin H, historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0) ≤ ∑ k : Fin K, ∑ h : Fin H, historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0) :=
          Finset.single_le_sum (f := fun k : Fin K => ∑ h : Fin H, historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0)) (fun k _ => Finset.sum_nonneg (fun h _ => by split_ifs <;> simp [hp]))
            (Finset.mem_univ k)
        rw [if_pos hb, mul_one] at h1
        linarith
      · have h1 : historyProb M L histT * (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0) ≤ ∑ Q : Qc, historyProb M L histT * (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0) :=
          Finset.single_le_sum (f := fun Q : Qc => historyProb M L histT * (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0)) (fun Q _ => by split_ifs <;> simp [hp]) (Finset.mem_univ Q)
        have h2 : ∑ Q : Qc, historyProb M L histT * (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0) ≤ ∑ h : Fin H, ∑ Q : Qc, historyProb M L histT * (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0) :=
          Finset.single_le_sum (f := fun h : Fin H => ∑ Q : Qc, historyProb M L histT * (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0)) (fun h _ => Finset.sum_nonneg (fun Q _ => by split_ifs <;> simp [hp]))
            (Finset.mem_univ h)
        have h3 : ∑ h : Fin H, ∑ Q : Qc, historyProb M L histT * (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0) ≤ ∑ k : Fin K, ∑ h : Fin H, ∑ Q : Qc, historyProb M L histT * (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0) :=
          Finset.single_le_sum (f := fun k : Fin K => ∑ h : Fin H, ∑ Q : Qc, historyProb M L histT * (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0)) (fun k _ => Finset.sum_nonneg (fun h _ => Finset.sum_nonneg (fun Q _ => by split_ifs <;> simp [hp])))
            (Finset.mem_univ k)
        rw [if_pos hb, mul_one] at h1
        linarith
  calc _ ≤ ∑ histT : Fin (K * n) → Trajectory S A H, (
        ∑ k : Fin K, ∑ h : Fin H, historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0) +
        ∑ k : Fin K, ∑ h : Fin H, ∑ Q : Qc, historyProb M L histT *
          (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0)) := Finset.sum_le_sum (fun histT _ => hpt histT)
    _ = ∑ k : Fin K, ∑ h : Fin H, ∑ histT : Fin (K * n) → Trajectory S A H, historyProb M L histT *
            (if β < ∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i q0) ^ 2
              then 1 else 0) +
        ∑ k : Fin K, ∑ h : Fin H, ∑ Q : Qc, ∑ histT : Fin (K * n) → Trajectory S A H, historyProb M L histT *
          (if (∑ i ∈ Finset.range k.1, (residualEst M qeval (List.ofFn histT) n h.1 i Q) ^ 2 ≤ β ∧
            4 * β < ∑ i ∈ Finset.range k.1, (Eres M qeval n β h.1 Q i (List.ofFn histT)) ^ 2)
            then 1 else 0) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_comm]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun h _ => ?_)
          rw [Finset.sum_comm]
    _ ≤ ∑ k : Fin K, ∑ h : Fin H, b2 + ∑ k : Fin K, ∑ h : Fin H, ∑ Q : Qc, δ1 := by
        refine add_le_add (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun h _ => ?_)))
          (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun Q _ => ?_))))
        · have hK1 : 1 ≤ K := by have := k.2; omega
          have hH1 : 1 ≤ H := by have := h.2; omega
          have hb := (bounds_real q hq2 H K hH1 hK1 δ hδ hδ1 (n * β) hnβ).2
          calc _ ≤ 2 ^ K * Real.exp (-(n * β / 6)) :=
                part2_prob M hM qeval hQ q0 hq0 hn β k.1 k.2.le h.2
            _ ≤ b2 := hb
        · have hK1 : 1 ≤ K := by have := k.2; omega
          have hH1 : 1 ≤ H := by have := h.2; omega
          have hb := (bounds_real q hq2 H K hH1 hK1 δ hδ hδ1 (n * β) hnβ).1
          have hq0' : 0 < q := by linarith
          have hδpos : 0 < δ1 := by
            have : (0 : ℝ) < H := by exact_mod_cast hH1
            have : (0 : ℝ) < K := by exact_mod_cast hK1
            positivity
          exact part1_prob M hM qeval hQ hn β k.1 k.2.le h.2 Q δ1 hδpos (by rw [hδ1def]; exact hb)
    _ ≤ δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        by_cases hKH : K = 0 ∨ H = 0
        · rcases hKH with h0 | h0 <;> simp [h0]
          all_goals linarith
        · push_neg at hKH
          have hK1 : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hKH.1
          have hH1 : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hKH.2
          have hq0' : 0 < q := by linarith
          have e1 : (K : ℝ) * (H * b2) = δ / 2 := by
            simp only [hb2]; field_simp
          have e2 : (K : ℝ) * (H * ((Fintype.card Qc : ℝ) * δ1)) = δ / 2 := by
            simp only [hδ1def, hq]; field_simp
          linarith

end E

theorem csv_core :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (_hM : RewardsNormalized M)
        {Qc : Type} [Fintype Qc] [Nonempty Qc] (_hQc : 1 < Fintype.card Qc)
        (qeval : Qc → ℕ → S → A → ℝ) (_hQ : IsNormalizedValueClass H qeval) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
        (n K : ℕ) (δ : ℝ), 0 < n → 0 < δ →
        ∀ β : ℝ, β = c * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n →
        probEvent M (biLinUCBLearner M qeval n β) (K * n)
            (fun histT =>
              ∀ k, k < K →
                (∀ Qf ∈ confSet M qeval (List.ofFn histT) n β k, ∀ h : Fin H,
                    ∑ i ∈ Finset.range k,
                      (bellmanResidual M (iterPolicy M qeval (List.ofFn histT) n β i) h.1
                        (qeval Qf)) ^ 2 ≤ C * β) ∧
                q0 ∈ confSet M qeval (List.ofFn histT) n β k)
          ≥ 1 - δ := by
  refine ⟨100, 4, by norm_num, by norm_num, ?_⟩
  intro S A _ _ _ _ _ H M hM Qc _ _ hQc qeval hQ q0 hq0 n K δ hn hδ β hβ
  exact main_bound M hM hQc qeval hQ q0 hq0 δ hn hδ β hβ

end FoundationsRL.FuncApprox

open FoundationsRL.FuncApprox
open FoundationsRL.RLBasics

theorem solution :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (_hM : RewardsNormalized M)
        {Qc : Type} [Fintype Qc] [Nonempty Qc] (_hQc : 1 < Fintype.card Qc)
        (qeval : Qc → ℕ → S → A → ℝ) (_hQ : IsNormalizedValueClass H qeval) (q0 : Qc)
        (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
        (n K : ℕ) (δ : ℝ), 0 < n → 0 < δ →
        ∀ β : ℝ, β = c * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n →
        probEvent M (biLinUCBLearner M qeval n β) (K * n)
            (fun histT =>
              ∀ k, k < K →
                (∀ Qf ∈ confSet M qeval (List.ofFn histT) n β k, ∀ h : Fin H,
                    ∑ i ∈ Finset.range k,
                      (bellmanResidual M (iterPolicy M qeval (List.ofFn histT) n β i) h.1
                        (qeval Qf)) ^ 2 ≤ C * β) ∧
                q0 ∈ confSet M qeval (List.ofFn histT) n β k)
          ≥ 1 - δ := by
  exact csv_core
