-- Prove2me | solution 1 for CountingLLL.ContractedWalk.pgf_reciprocal_expectation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:23:16.859192+00:00
-- url     : https://prove2.me/submissions/f735fea2-1344-4bac-9aa9-4b951a33c2bc

import Mathlib

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Interval

theorem solution {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (K : β → ℕ) (hK : Measurable K) :
    (∫ x, (1:ℝ)/((K x : ℝ)+1) ∂ν) = ∫ z in (0:ℝ)..1, ∫ x, z ^ K x ∂ν := by
  classical
  let σ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)
  let Q : ℝ × β → ℝ := fun x => if x.1 ∈ Set.Icc (0:ℝ) 1 then x.1 ^ K x.2 else 0
  have hQ : Measurable Q := by
    apply Measurable.ite (measurableSet_Icc.preimage measurable_fst)
    · exact measurable_fst.pow (hK.comp measurable_snd)
    · exact measurable_const
  have hQInt : Integrable Q (σ.prod ν) := by
    apply (integrable_const (1:ℝ)).mono' hQ.aestronglyMeasurable
    filter_upwards with x
    by_cases hx : x.1 ∈ Set.Icc (0:ℝ) 1
    · simp only [Q, if_pos hx, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1 _)]
      exact pow_le_one₀ hx.1 hx.2
    · simp only [Q, if_neg hx, norm_zero, zero_le_one]
  have hQinner (z : ℝ) (hz : z ∈ Set.Ioc (0:ℝ) 1) :
      (∫ x, Q (z,x) ∂ν) = ∫ x, z ^ K x ∂ν := by
    congr 1
    funext x
    simp only [Q, if_pos (Set.Ioc_subset_Icc_self hz)]
  have hQouter (x : β) : (∫ z, Q (z,x) ∂σ) = (1:ℝ)/((K x : ℝ)+1) := by
    have hEq : (∫ z, Q (z,x) ∂σ) = ∫ z, z ^ K x ∂σ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      simp only [Q, if_pos (Set.Ioc_subset_Icc_self hz)]
    rw [hEq, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [integral_pow]
    simp
  have houter : (∫ z, ∫ x, Q (z,x) ∂ν ∂σ) = ∫ z in (0:ℝ)..1, ∫ x, z ^ K x ∂ν := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact hQinner z hz
  calc
    _ = ∫ x, ∫ z, Q (z,x) ∂σ ∂ν := by simp_rw [hQouter]
    _ = ∫ w, Q w ∂(σ.prod ν) := (integral_prod_symm Q hQInt).symm
    _ = ∫ z, ∫ x, Q (z,x) ∂ν ∂σ := integral_prod Q hQInt
    _ = _ := houter
