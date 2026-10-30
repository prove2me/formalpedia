-- Prove2me | solution 1 for GenCostSched.GFCS.betahat_dual_feasible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:46:34.203998+00:00
-- url     : https://prove2.me/submissions/9991d1e5-7660-4670-975b-0046ff4b09e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model
import Theorems.Thm_GenCostSched_GFCS_lemma_5
import Theorems.Thm_GenCostSched_GFCS_eq_20

open MeasureTheory Set
open scoped ENNReal

namespace GFCSBhdfAux
open GenCostSched.GFCS

variable {n : ℕ}

theorem mem_aliveOld {I : Instance n} {y : Fin n → ℝ → ℝ} {k j : Fin n} :
    j ∈ I.aliveOld y k ↔ j < k ∧ 0 < I.residual y k j := by
  simp [Instance.aliveOld]

theorem tailFrom_of_le {m : ℕ} {s t : ℝ} (x : Fin m → ℝ → ℝ) (j : Fin m) (h : s ≤ t) :
    tailFrom s x j t = x j t := by
  simp [tailFrom, indicator_of_mem (mem_Ici.2 h)]

theorem tailFrom_of_lt {m : ℕ} {s t : ℝ} (x : Fin m → ℝ → ℝ) (j : Fin m) (h : t < s) :
    tailFrom s x j t = 0 := by
  simp [tailFrom, indicator_of_notMem (show t ∉ Ici s from fun h' => absurd (mem_Ici.1 h') (not_le.2 h))]

/-- Basic invariants of a run of Algorithm 2. -/
theorem run_inv (I : Instance n) (hI : I.Standing) (X : ℕ → Fin n → ℝ → ℝ)
    (hX : I.IsAlg2Run X) : ∀ i, i ≤ n →
    (∀ j, Measurable (X i j)) ∧ (∀ j t, X i j t = 0 ∨ X i j t = 1) ∧
    (∀ t, ∑ j, X i j t ≤ 1) ∧ (∀ j t, t < I.r j → X i j t = 0) ∧
    (∀ j : Fin n, i ≤ j.val → ∀ t, X i j t = 0) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hX.1]
    refine ⟨fun j => measurable_const, fun j t => Or.inl rfl, fun t => by simp,
      fun j t _ => rfl, fun j _ t => rfl⟩
    -- unreachable
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih (by omega)
    set k : Fin n := ⟨i, by omega⟩ with hk
    obtain ⟨hbef, hopt, _⟩ := hX.2 k
    have hkv : k.val = i := rfl
    rw [hkv] at hbef hopt
    obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hopt.1
    have hrep : ∀ j t, X (i+1) j t =
        if t < I.r k then X i j t else tailFrom (I.r k) (X (i+1)) j t := by
      intro j t
      split_ifs with h
      · exact hbef j t h
      · exact (tailFrom_of_le _ _ (le_of_not_gt h)).symm
    have hout : ∀ j : Fin n, j ∉ insert k (I.aliveOld (X i) k) → ∀ t,
        tailFrom (I.r k) (X (i+1)) j t = 0 := fun j hj t => o4 j hj t
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      have : X (i+1) j = (Iio (I.r k)).piecewise (X i j) (tailFrom (I.r k) (X (i+1)) j) := by
        funext t
        rw [hrep j t]
        by_cases h : t < I.r k
        · simp [h, Set.piecewise, mem_Iio]
        · simp [h, Set.piecewise, mem_Iio]
      rw [this]
      exact Measurable.piecewise measurableSet_Iio (ih1 j) (o1 j)
    · intro j t
      rw [hrep j t]; split_ifs
      · exact ih2 j t
      · exact o2 j t
    · intro t
      by_cases h : t < I.r k
      · simp only [hrep _ t, h, if_true]; exact ih3 t
      · simp only [hrep _ t, h, if_false]; exact o5 t
    · intro j t ht
      rw [hrep j t]; split_ifs with h
      · exact ih4 j t ht
      · apply hout j _ t
        intro hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact h ht
        · have hjk := (mem_aliveOld.1 hj).1
          exact h (lt_of_lt_of_le ht (hI.2 hjk.le))
    · intro j hj t
      rw [hrep j t]; split_ifs with h
      · exact ih5 j (by omega) t
      · apply hout j _ t
        intro hj'
        rcases Finset.mem_insert.1 hj' with h' | h'
        · rw [h'] at hj; simp [k] at hj
        · have := (mem_aliveOld.1 h').1
          have : j.val < i := this
          omega

theorem gp_nonneg {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j) (t : ℝ)
    (ht : I.r j ≤ t) : 0 ≤ I.g' j t := by
  have hd := hj.2.2.2.2.2 t ht
  have hmono := hj.2.2.2.1
  have := hmono.derivWithin_nonneg (x := t)
  rwa [hd.derivWithin (uniqueDiffOn_Ici _ t (mem_Ici.2 ht))] at this

theorem gp_int {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j) (a b : ℝ)
    (ha : I.r j ≤ a) : IntegrableOn (I.g' j) (Icc a b) := by
  have hd := hj.2.2.2.2.2
  have hcont : ContinuousOn (I.g j) (Icc a b) := by
    intro t ht
    exact ((hd t (ha.trans ht.1)).continuousWithinAt).mono
      (fun u hu => mem_Ici.2 (ha.trans hu.1))
  have h1 : IntegrableOn (I.g' j) (Ioc a b) := by
    apply intervalIntegral.integrableOn_deriv_of_nonneg hcont
    · intro t ht
      exact (hd t (ha.trans ht.1.le)).hasDerivAt (Ici_mem_nhds (lt_of_le_of_lt ha ht.1))
    · intro t ht
      exact gp_nonneg I j hj t (ha.trans ht.1.le)
  exact (integrableOn_Icc_iff_integrableOn_Ioc).2 h1

/-- Integrability and nonnegativity of `β̂` for an integral schedule. -/
theorem BH_int {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s)
    (x : Fin m → ℝ → ℝ) (hx : IsOffIntSched s A ρ x) :
    IntegrableOn (betaHat I.g' x) (Ici s) ∧ (∀ t, 0 ≤ betaHat I.g' x t) ∧
      (∀ ℓ, Integrable (fun τ => I.g' ℓ τ * x ℓ τ)) := by
  obtain ⟨x1, x2, x3, x4, x5, x6, ⟨T0, hT0⟩⟩ := hx
  set T := max T0 s
  have hT : ∀ j t, T < t → x j t = 0 := fun j t ht => hT0 j t (lt_of_le_of_lt (le_max_left _ _) ht)
  have hfnn : ∀ ℓ τ, 0 ≤ I.g' ℓ τ * x ℓ τ := by
    intro ℓ τ
    rcases x2 ℓ τ with h | h
    · simp [h]
    · rw [h, mul_one]
      have hℓ : ℓ ∈ A := by
        by_contra hc; rw [x4 ℓ hc τ] at h; exact zero_ne_one h
      have hτ : s ≤ τ := by
        by_contra hc; rw [x3 ℓ τ (lt_of_not_ge hc)] at h; exact zero_ne_one h
      exact gp_nonneg I ℓ (hI ℓ) τ ((hA ℓ hℓ).trans hτ)
  have hfint : ∀ ℓ, Integrable (fun τ => I.g' ℓ τ * x ℓ τ) := by
    intro ℓ
    by_cases hℓ : ℓ ∈ A
    · have hi := (gp_int I ℓ (hI ℓ) s T (hA ℓ hℓ)).integrable_indicator measurableSet_Icc
      have h2 : Integrable (fun τ => (Icc s T).indicator (I.g' ℓ) τ * x ℓ τ) := by
        refine hi.mul_bdd (c := 1) (x1 ℓ).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall (fun τ => ?_)
        rcases x2 ℓ τ with h | h <;> simp [h]
      refine h2.congr (Filter.Eventually.of_forall (fun τ => ?_))
      dsimp only
      by_cases hτ : τ ∈ Icc s T
      · simp [indicator_of_mem hτ]
      · rw [indicator_of_notMem hτ]
        simp only [mem_Icc, not_and_or, not_le] at hτ
        rcases hτ with h | h
        · simp [x3 ℓ τ h]
        · simp [hT ℓ τ h]
    · have : (fun τ => I.g' ℓ τ * x ℓ τ) = fun _ => 0 := by
        funext τ; simp [x4 ℓ hℓ τ]
      rw [this]; exact integrable_zero _ _ _
  have hanti : Antitone (betaHat I.g' x) := by
    intro t t' htt
    apply Finset.sum_le_sum
    intro ℓ _
    apply setIntegral_mono_set (hfint ℓ).integrableOn
    · exact Filter.Eventually.of_forall (fun τ => hfnn ℓ τ)
    · exact (Ioi_subset_Ioi htt).eventuallyLE
  have hnn : ∀ t, 0 ≤ betaHat I.g' x t := by
    intro t
    apply Finset.sum_nonneg
    intro ℓ _
    exact setIntegral_nonneg measurableSet_Ioi (fun τ _ => hfnn ℓ τ)
  have hzero : ∀ t, T ≤ t → betaHat I.g' x t = 0 := by
    intro t ht
    apply Finset.sum_eq_zero
    intro ℓ _
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro τ hτ
    simp [hT ℓ τ (lt_of_le_of_lt ht hτ)]
  refine ⟨?_, hnn, hfint⟩
  have hbd : IntegrableOn (betaHat I.g' x) (Icc s T) := by
    refine Measure.integrableOn_of_bounded (M := betaHat I.g' x s) (by simp)
      hanti.measurable.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun t ht => ?_))
    rw [Real.norm_of_nonneg (hnn t)]
    exact hanti ht.1
  refine hbd.of_forall_sdiff_eq_zero measurableSet_Ici ?_
  intro t ht
  apply hzero
  by_contra hc
  exact ht.2 ⟨mem_Ici.1 ht.1, le_of_not_ge hc⟩

theorem optInt_eq {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ)
    (x : Fin m → ℝ → ℝ) (hx : IsOptIntegral G s A ρ x) : offCost G x = rnf G s A ρ := by
  obtain ⟨⟨x1, x2, x3, x4, x5, x6, _⟩, hopt⟩ := hx
  have hfr : IsOffFracSched s A ρ x := by
    refine ⟨x1, fun j t => ?_, x3, x4, x5, fun j hj => (x6 j hj).symm.le⟩
    rcases x2 j t with h | h <;> simp [h]
  apply le_antisymm
  · exact le_sInf (by rintro _ ⟨y, hy, rfl⟩; exact hopt y hy)
  · exact sInf_le ⟨x, hfr, rfl⟩

theorem bh_tail {m : ℕ} (gp : Fin m → ℝ → ℝ) (s : ℝ) (x : Fin m → ℝ → ℝ) (t : ℝ)
    (ht : s ≤ t) : betaHat gp (tailFrom s x) t = betaHat gp x t := by
  unfold betaHat
  apply Finset.sum_congr rfl
  intro ℓ _
  apply setIntegral_congr_fun measurableSet_Ioi
  intro τ hτ
  dsimp only
  rw [tailFrom_of_le _ _ (ht.trans (le_of_lt hτ))]

theorem bh_ae {m : ℕ} (gp : Fin m → ℝ → ℝ) (x y : Fin m → ℝ → ℝ)
    (h : ∀ ℓ, x ℓ =ᵐ[volume] y ℓ) (t : ℝ) : betaHat gp x t = betaHat gp y t := by
  unfold betaHat
  apply Finset.sum_congr rfl
  intro ℓ _
  apply integral_congr_ae
  apply ae_restrict_of_ae
  filter_upwards [h ℓ] with τ hτ
  rw [hτ]

theorem seg_eq (I : Instance n) (hmono : Monotone I.r) (k : Fin n) :
    I.segment k = Ici (I.r k) \ (if h : k.val + 1 < n then Ici (I.r ⟨k.val + 1, h⟩) else ∅) := by
  ext t
  simp only [Instance.segment, mem_setOf_eq, mem_diff, mem_Ici]
  split_ifs with h
  · simp only [mem_Ici, not_le]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 ⟨k.val + 1, h⟩ (by rw [Fin.lt_def]; simp)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k' hk' => lt_of_lt_of_le h2 (hmono ?_)⟩
      rw [Fin.le_def]; rw [Fin.lt_def] at hk'; simp; omega
  · simp only [notMem_empty, not_false_eq_true, and_true]
    constructor
    · exact fun h' => h'.1
    · intro h1
      refine ⟨h1, fun k' hk' => ?_⟩
      exfalso; rw [Fin.lt_def] at hk'; have := k'.isLt; omega

end GFCSBhdfAux

open GenCostSched.GFCS GFCSBhdfAux in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing)
    (X : ℕ → Fin n → ℝ → ℝ) (hX : I.IsAlg2Run X) (A : Fin n → Fin n → ℝ) (B : Fin n → ℝ → ℝ)
    (hAB : ∀ k : Fin n, IsOffOptDual I.g (I.r k) (insert k (I.aliveOld (X k.val) k))
      (I.residual (X k.val) k) (A k) (B k)) :
    I.IsDualFeas (fun k => A k k)
      (I.concatDual (fun k => betaHat I.g' (X (k.val + 1)))) := by
  have hJS : ∀ j, I.JobStanding j := hI.1
  have hAl_lt : ∀ (k j : Fin n), j ∈ I.aliveOld (X k.val) k → j < k :=
    fun k j hj => (mem_aliveOld.1 hj).1
  have hAk : ∀ k : Fin n, ∀ j ∈ insert k (I.aliveOld (X k.val) k), I.r j ≤ I.r k := by
    intro k j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact le_rfl
    · exact hI.2 (hAl_lt k j hj).le
  have hkk : ∀ k : Fin n, I.residual (X k.val) k k = I.v k := by
    intro k
    have h5 := (run_inv I hI X hX k.val k.isLt.le).2.2.2.2 k le_rfl
    simp only [Instance.residual]
    rw [setIntegral_congr_fun measurableSet_Iio (g := fun _ => (0:ℝ)) (fun t _ => h5 t)]
    simp
  have hρpos : ∀ k : Fin n, ∀ j ∈ insert k (I.aliveOld (X k.val) k),
      0 < I.residual (X k.val) k j := by
    intro k j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · rw [hkk]; exact (hJS j).1
    · exact (mem_aliveOld.1 hj).2
  have hxn : ∀ k : Fin n, IsOptIntegral I.g (I.r k) (insert k (I.aliveOld (X k.val) k))
      (I.residual (X k.val) k) (tailFrom (I.r k) (X (k.val + 1))) := fun k => (hX.2 k).2.1
  set b : Fin n → ℝ → ℝ := fun k => betaHat I.g' (X (k.val + 1)) with hbdef
  have hb_eq : ∀ k : Fin n, ∀ t, I.r k ≤ t →
      b k t = betaHat I.g' (tailFrom (I.r k) (X (k.val + 1))) t :=
    fun k t ht => (bh_tail I.g' (I.r k) (X (k.val + 1)) t ht).symm
  have hBH := fun k : Fin n => BH_int I hJS _ _ _ (hAk k) _ (hxn k).1
  have hbint : ∀ k : Fin n, IntegrableOn (b k) (Ici (I.r k)) := fun k =>
    (hBH k).1.congr_fun (fun t ht => (hb_eq k t (mem_Ici.1 ht)).symm) measurableSet_Ici
  have hsegm : ∀ k : Fin n, MeasurableSet (I.segment k) := by
    intro k; rw [seg_eq I hI.2 k]; split_ifs
    · exact measurableSet_Ici.diff measurableSet_Ici
    · exact measurableSet_Ici.diff MeasurableSet.empty
  have hsegsub : ∀ k : Fin n, I.segment k ⊆ Ici (I.r k) := fun k t ht => mem_Ici.2 ht.1
  have L5 := lemma_5 I hI X hX A B hAB
  have E20 : ∀ k : Fin n, ∀ᵐ t, I.r k ≤ t →
      B k t ≤ betaHat I.g' (tailFrom (I.r k) (X (k.val + 1))) t := fun k =>
    eq_20 I hJS (I.r k) _ _ (hAk k) (hρpos k) _ (hxn k) (A k) (B k) (hAB k)
  have hall := ae_all_iff.2 E20
  refine ⟨?_, fun k => L5.2.1 k, ?_, ?_⟩
  · unfold Instance.concatDual
    exact integrable_finset_sum _ (fun k _ =>
      (((hbint k).mono_set (hsegsub k)).integrable_indicator (hsegm k)).integrableOn)
  · refine Filter.Eventually.of_forall (fun t _ => ?_)
    unfold Instance.concatDual
    apply Finset.sum_nonneg
    intro k _
    by_cases ht : t ∈ I.segment k
    · rw [indicator_of_mem ht, hb_eq k t (hsegsub k ht)]
      exact (hBH k).2.1 t
    · rw [indicator_of_notMem ht]
  · intro j
    filter_upwards [L5.2.2.2 j, hall] with t h1 h3
    intro hjt
    have h1' := h1 hjt
    have hle : I.concatDual B t ≤ I.concatDual b t := by
      unfold Instance.concatDual
      apply Finset.sum_le_sum
      intro k _
      by_cases ht : t ∈ I.segment k
      · rw [indicator_of_mem ht, indicator_of_mem ht, hb_eq k t (hsegsub k ht)]
        exact h3 k (hsegsub k ht)
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]
    linarith
