-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_levy_signed_mark_band_generic_integrand_finite_annulus_chain_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:07:06.06443+00:00
-- url     : https://prove2.me/submissions/b8755c6f-e13d-47b2-88ba-99da8d2a78d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (a : ℕ → ℝ) (ha : Monotone a)
    (f : ℝ → ℝ) (n m : ℕ) (hnm : n ≤ m)
    (hInt : IntegrableOn f (Ioc (a n) (a m)) ν) :
    (∫ z in Ioc (a n) (a m), f z ∂ν) =
      ∑ i ∈ Finset.Ico n m,
        (∫ z in Ioc (a i) (a (i + 1)), f z ∂ν) := by
  classical
  revert hInt
  induction m, hnm using Nat.le_induction with
  | base =>
      intro hInt
      simp
  | succ m hnm ih =>
      intro hInt
      have hPrev :
          IntegrableOn f (Ioc (a n) (a m)) ν := by
        apply hInt.mono_set
        intro z hz
        exact ⟨hz.1, le_trans hz.2 (ha (Nat.le_succ m))⟩
      have hRight :
          IntegrableOn f
            (Ioc (a m) (a (m + 1))) ν := by
        apply hInt.mono_set
        intro z hz
        exact ⟨lt_of_le_of_lt (ha hnm) hz.1, hz.2⟩
      have hDisj : Disjoint (Ioc (a n) (a m)) (Ioc (a m) (a (m + 1))) := by
        apply Set.disjoint_left.mpr
        intro z hz ht
        exact (not_lt_of_ge hz.2) ht.1
      have hSplit :
          (∫ z in Ioc (a n) (a (m + 1)), f z ∂ν) =
          (∫ z in Ioc (a n) (a m), f z ∂ν) +
          (∫ z in Ioc (a m) (a (m + 1)), f z ∂ν) := by
        rw [← Set.Ioc_union_Ioc_eq_Ioc (ha hnm) (ha (Nat.le_succ m))]
        exact setIntegral_union hDisj measurableSet_Ioc hPrev hRight
      calc
        (∫ z in Ioc (a n) (a (m + 1)), f z ∂ν) =
          (∫ z in Ioc (a n) (a m), f z ∂ν) +
          (∫ z in Ioc (a m) (a (m + 1)), f z ∂ν) := hSplit
        _ = (∑ i ∈ Finset.Ico n m,
          (∫ z in Ioc (a i) (a (i + 1)), f z ∂ν)) +
          (∫ z in Ioc (a m) (a (m + 1)), f z ∂ν) := by
            rw [ih hPrev]
        _ = ∑ i ∈ Finset.Ico n (m + 1),
          (∫ z in Ioc (a i) (a (i + 1)), f z ∂ν) := by
            rw [Finset.sum_Ico_succ_top hnm]
