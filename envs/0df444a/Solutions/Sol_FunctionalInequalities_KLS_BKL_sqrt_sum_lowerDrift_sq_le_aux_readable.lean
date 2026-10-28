-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.sqrt_sum_lowerDrift_sq_le_aux_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:44.258628+00:00
-- url     : https://prove2.me/submissions/3be893fc-5222-4c6f-b8d2-aa737a4fbb12

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Theorems.Thm_FunctionalInequalities_KLS_BKL_sqrt_sum_sq_sum_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_sum_selected_eq_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_sum_sq_pairTerm_ofFn_le_readable

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S4Section6Pointwise
variable {n : ℕ}
section Masks
theorem FunctionalInequalities.KLS.BKL.selected_succ {E : Type*} {k : ℕ} (h : Fin (k+1) → E) (q : Fin (k+1) → Bool) :
    selected h q = if q 0 = true then h 0 :: selected (Fin.tail h) (Fin.tail q)
      else selected (Fin.tail h) (Fin.tail q) := by
  simp [selected]
theorem FunctionalInequalities.KLS.BKL.selected_zero {E : Type*} (h : Fin 0 → E) (q : Fin 0 → Bool) : selected h q = [] := by
  simp [selected]
theorem FunctionalInequalities.KLS.BKL.maskCount_succ {k : ℕ} (q : Fin (k+1) → Bool) :
    maskCount q = (if q 0 = true then 1 else 0) + maskCount (Fin.tail q) := by
  rw [maskCount, maskCount, Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  rfl
theorem FunctionalInequalities.KLS.BKL.maskCount_zero (q : Fin 0 → Bool) : maskCount q = 0 := by
  simp [maskCount]
theorem FunctionalInequalities.KLS.BKL.tail_not {k : ℕ} (q : Fin (k+1) → Bool) :
    Fin.tail (fun i => !(q i)) = fun i => !(Fin.tail q i) := rfl
theorem FunctionalInequalities.KLS.BKL.maskCount_add_compl {k : ℕ} (q : Fin k → Bool) :
    maskCount q + maskCount (fun i => !(q i)) = k := by
  induction k with
  | zero => simp [maskCount_zero]
  | succ k ih =>
    rw [maskCount_succ, maskCount_succ (fun i => !(q i)), tail_not]
    have := ih (Fin.tail q)
    cases q 0 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> omega
theorem FunctionalInequalities.KLS.BKL.selected_length {E : Type*} {k : ℕ} (h : Fin k → E) (q : Fin k → Bool) :
    (selected h q).length = maskCount q := by
  induction k with
  | zero => simp [selected_zero, maskCount_zero]
  | succ k ih =>
    rw [selected_succ, maskCount_succ]
    cases hq : q 0 <;> simp [ih, add_comm]
theorem FunctionalInequalities.KLS.BKL.card_masks (k c : ℕ) :
    (Finset.univ.filter fun q : Fin k → Bool => maskCount q = c).card = k.choose c := by
  classical
  have h := Finset.card_powersetCard c (Finset.univ : Finset (Fin k))
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine Finset.card_nbij' (fun q => Finset.univ.filter fun i => q i = true)
    (fun s i => decide (i ∈ s)) ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hq.2⟩
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show (Finset.univ.filter fun i => decide (i ∈ s) = true).card = c
    rw [← hs.2]
    congr 1
    ext i
    simp
  · intro q _
    funext i
    simp
  · intro s _
    ext i
    simp
theorem FunctionalInequalities.KLS.BKL.card_masks_true (k c : ℕ) :
    (Finset.univ.filter fun q : Fin (k+1) → Bool => q 0 = true ∧ maskCount q = c + 1).card =
      k.choose c := by
  classical
  rw [← card_masks k c]
  refine Finset.card_nbij' (fun q => Fin.tail q) (fun q => Fin.cons true q) ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h2 := hq.2.2
    rw [maskCount_succ, hq.2.1] at h2
    simp only [if_true] at h2
    show maskCount (Fin.tail q) = c
    omega
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [maskCount_succ]
    simp [hq.2, add_comm]
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    simp only
    rw [← hq.2.1]
    exact Fin.cons_self_tail q
  · intro q _
    simp only
    simp
end Masks
section Algebra
theorem FunctionalInequalities.KLS.BKL.lowerDrift_eq_sum_middleMasks (ν : Measure (EuclideanSpace ℝ (Fin n))) {k : ℕ}
    (h : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) :
    lowerDrift ν h 0 = ∑ q ∈ middleMasks k, maskTerm ν h q := by
  unfold lowerDrift middleMasks maskTerm
  simp only [selected_length]
/-- The Section 6 pointwise bound with `m = k + 1`. -/
theorem solution (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hA : IsUnit (FunctionalInequalities.Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪FunctionalInequalities.Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (k : ℕ) (b : ℕ → ℝ)
    (h100 : ∀ r, 2 ≤ r → r < k + 1 → ∀ v : EuclideanSpace ℝ (Fin n),
      FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r - 1) v ≤
        b r * ⟪FunctionalInequalities.Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (u : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∑ J : Fin k → Fin n,
        FunctionalInequalities.KLS.BKL.lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n)))
          (Fin.cons u fun i => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
            (EuclideanSpace.basisFun (Fin n) ℝ (J i)) : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) 0 ^ 2) ≤
      ∑ a ∈ Finset.Icc 2 (k - 1), (k.choose (a - 1) : ℝ) *
        Real.sqrt (b (k + 2 - a) * FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u) := by
  change Real.sqrt (∑ J : Fin k → Fin n,
      FunctionalInequalities.KLS.BKL.lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n)))
        (Fin.cons u fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
          Fin (k + 1) → EuclideanSpace ℝ (Fin n)) 0 ^ 2) ≤ _
  simp only [FunctionalInequalities.KLS.BKL.lowerDrift_eq_sum_middleMasks]
  have hmaps : ∀ q ∈ FunctionalInequalities.KLS.BKL.middleMasks k, FunctionalInequalities.KLS.BKL.maskCount q ∈ Finset.Icc 2 (k - 1) := by
    intro q hq
    rw [FunctionalInequalities.KLS.BKL.middleMasks, Finset.mem_filter] at hq
    have := FunctionalInequalities.KLS.BKL.maskCount_add_compl q
    rw [Finset.mem_Icc]
    omega
  have hcard : ∀ a ∈ Finset.Icc 2 (k - 1),
      ((FunctionalInequalities.KLS.BKL.middleMasks k).filter fun q => FunctionalInequalities.KLS.BKL.maskCount q = a).card = k.choose (a - 1) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel, ← FunctionalInequalities.KLS.BKL.card_masks_true k a']
    congr 1
    ext q
    simp only [FunctionalInequalities.KLS.BKL.middleMasks, Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and]
    have := FunctionalInequalities.KLS.BKL.maskCount_add_compl q
    constructor
    · rintro ⟨⟨h0, -, -⟩, h⟩
      exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨h0, by omega, by omega⟩, h⟩
  have hmask : ∀ q ∈ FunctionalInequalities.KLS.BKL.middleMasks k,
      ∑ J : Fin k → Fin n, FunctionalInequalities.KLS.BKL.maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n)))
        (Fin.cons u fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
          Fin (k + 1) → EuclideanSpace ℝ (Fin n)) q ^ 2 ≤
        b (k + 2 - FunctionalInequalities.KLS.BKL.maskCount q) * FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (FunctionalInequalities.KLS.BKL.maskCount q) u := by
    intro q hq
    rw [FunctionalInequalities.KLS.BKL.middleMasks, Finset.mem_filter] at hq
    obtain ⟨-, hq0, hq2, hq2'⟩ := hq
    have hcnt := FunctionalInequalities.KLS.BKL.maskCount_succ q
    simp only [hq0, ↓reduceIte] at hcnt
    have hcnt' := FunctionalInequalities.KLS.BKL.maskCount_succ (fun i => !(q i))
    rw [FunctionalInequalities.KLS.BKL.tail_not] at hcnt'
    simp only [hq0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, zero_add] at hcnt'
    have hsum := FunctionalInequalities.KLS.BKL.maskCount_add_compl (Fin.tail q)
    have hterm : ∀ J : Fin k → Fin n,
        FunctionalInequalities.KLS.BKL.maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n)))
          (Fin.cons u fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
            Fin (k + 1) → EuclideanSpace ℝ (Fin n)) q ^ 2 =
        FunctionalInequalities.KLS.BKL.pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) u
          (FunctionalInequalities.Analysis.selected (fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i)) (Fin.tail q))
          (FunctionalInequalities.Analysis.selected (fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i))
            (fun i => !(Fin.tail q i))) := by
      intro J
      simp only [FunctionalInequalities.KLS.BKL.maskTerm, FunctionalInequalities.KLS.BKL.pairTerm]
      rw [FunctionalInequalities.KLS.BKL.selected_succ, FunctionalInequalities.KLS.BKL.selected_succ (q := fun i => !(q i)), FunctionalInequalities.KLS.BKL.tail_not]
      simp only [hq0, Fin.cons_zero, Fin.tail_cons, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.sum_congr rfl fun J _ => hterm J,
      FunctionalInequalities.KLS.BKL.sum_selected_eq_readable (FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n)))) k (Fin.tail q)
        (FunctionalInequalities.KLS.BKL.pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) u) _ _ rfl rfl, hcnt]
    have hβ : k + 2 - (1 + FunctionalInequalities.KLS.BKL.maskCount (Fin.tail q)) = FunctionalInequalities.KLS.BKL.maskCount (fun i => !(Fin.tail q i)) + 1 := by omega
    rw [hβ, add_comm 1]
    refine FunctionalInequalities.KLS.BKL.sum_sq_pairTerm_ofFn_le_readable ν hc hA hApos _ (fun v => ?_) u
    simpa using h100 (FunctionalInequalities.KLS.BKL.maskCount (fun i => !(Fin.tail q i)) + 1) (by omega) (by omega) v
  calc Real.sqrt (∑ J : Fin k → Fin n, (∑ q ∈ FunctionalInequalities.KLS.BKL.middleMasks k,
          FunctionalInequalities.KLS.BKL.maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n)))
            (Fin.cons u fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
              Fin (k + 1) → EuclideanSpace ℝ (Fin n)) q) ^ 2)
      ≤ ∑ q ∈ FunctionalInequalities.KLS.BKL.middleMasks k, Real.sqrt (∑ J : Fin k → Fin n,
          FunctionalInequalities.KLS.BKL.maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n)))
            (Fin.cons u fun i => FunctionalInequalities.KLS.BKL.sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J i) :
              Fin (k + 1) → EuclideanSpace ℝ (Fin n)) q ^ 2) :=
        FunctionalInequalities.KLS.BKL.sqrt_sum_sq_sum_le_readable (FunctionalInequalities.KLS.BKL.middleMasks k) _
    _ ≤ ∑ q ∈ FunctionalInequalities.KLS.BKL.middleMasks k, Real.sqrt (b (k + 2 - FunctionalInequalities.KLS.BKL.maskCount q) *
          FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (FunctionalInequalities.KLS.BKL.maskCount q) u) :=
        Finset.sum_le_sum fun q hq => Real.sqrt_le_sqrt (hmask q hq)
    _ = ∑ a ∈ Finset.Icc 2 (k - 1), ∑ q ∈ (FunctionalInequalities.KLS.BKL.middleMasks k).filter (fun q => FunctionalInequalities.KLS.BKL.maskCount q = a),
          Real.sqrt (b (k + 2 - a) * FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u) :=
        (Finset.sum_fiberwise_of_maps_to' hmaps
          (fun a => Real.sqrt (b (k + 2 - a) *
            FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u))).symm
    _ = ∑ a ∈ Finset.Icc 2 (k - 1), (k.choose (a - 1) : ℝ) *
          Real.sqrt (b (k + 2 - a) * FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Finset.sum_const, nsmul_eq_mul, hcard a ha]
