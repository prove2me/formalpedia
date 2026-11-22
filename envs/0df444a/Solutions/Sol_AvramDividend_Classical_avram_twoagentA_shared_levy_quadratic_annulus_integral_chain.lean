-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_shared_levy_quadratic_annulus_integral_chain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:40:27.402495+00:00
-- url     : https://prove2.me/submissions/5339ae45-4e94-423a-82fb-179730b94b76

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (a : ℕ → ℝ) (ha : Monotone a)
    (n m : ℕ) (hnm : n ≤ m)
    (hInt : IntegrableOn (fun z : ℝ => z ^ 2) (Ioc (a n) (a m)) ν) :
    (∫ z in Ioc (a n) (a m), z ^ 2 ∂ν) =
      ∑ i ∈ Finset.Ico n m,
        (∫ z in Ioc (a i) (a (i + 1)), z ^ 2 ∂ν) := by
  classical
  revert hInt
  induction m, hnm using Nat.le_induction with
  | base =>
      intro hInt
      simp
  | succ m hnm ih =>
      intro hInt
      have hPrev :
          IntegrableOn (fun z : ℝ => z ^ 2) (Ioc (a n) (a m)) ν := by
        apply hInt.mono_set
        intro z hz
        exact ⟨hz.1, le_trans hz.2 (ha (Nat.le_succ m))⟩
      have hRight :
          IntegrableOn (fun z : ℝ => z ^ 2)
            (Ioc (a m) (a (m + 1))) ν := by
        apply hInt.mono_set
        intro z hz
        exact ⟨lt_of_le_of_lt (ha hnm) hz.1, hz.2⟩
      have hDisj : Disjoint (Ioc (a n) (a m)) (Ioc (a m) (a (m + 1))) := by
        apply Set.disjoint_left.mpr
        intro z hz ht
        exact (not_lt_of_ge hz.2) ht.1
      have hSplit :
          (∫ z in Ioc (a n) (a (m + 1)), z ^ 2 ∂ν) =
          (∫ z in Ioc (a n) (a m), z ^ 2 ∂ν) +
          (∫ z in Ioc (a m) (a (m + 1)), z ^ 2 ∂ν) := by
        rw [← Set.Ioc_union_Ioc_eq_Ioc (ha hnm) (ha (Nat.le_succ m))]
        exact setIntegral_union hDisj measurableSet_Ioc hPrev hRight
      calc
        (∫ z in Ioc (a n) (a (m + 1)), z ^ 2 ∂ν) =
          (∫ z in Ioc (a n) (a m), z ^ 2 ∂ν) +
          (∫ z in Ioc (a m) (a (m + 1)), z ^ 2 ∂ν) := hSplit
        _ = (∑ i ∈ Finset.Ico n m,
          (∫ z in Ioc (a i) (a (i + 1)), z ^ 2 ∂ν)) +
          (∫ z in Ioc (a m) (a (m + 1)), z ^ 2 ∂ν) := by
            rw [ih hPrev]
        _ = ∑ i ∈ Finset.Ico n (m + 1),
          (∫ z in Ioc (a i) (a (i + 1)), z ^ 2 ∂ν) := by
            rw [Finset.sum_Ico_succ_top hnm]
