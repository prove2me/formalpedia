-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_weak_limit_of_tight_approximants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:32:33.990855+00:00
-- url     : https://prove2.me/submissions/c45f084c-e22f-4de2-b583-4d10a831bd03

import Mathlib.MeasureTheory.Measure.Prokhorov
import Theorems.Thm_AvramDividend_Classical_excursion_fixed_mass_finite_measure_family
import Theorems.Thm_AvramDividend_Classical_excursion_fixed_mass_normalized_prokhorov_subsequence
import Theorems.Thm_AvramDividend_Classical_excursion_rescale_normalized_weak_limit
import Theorems.Thm_AvramDividend_Classical_excursion_finite_measure_normalize_nonnegative_support
import Theorems.Thm_AvramDividend_Classical_excursion_probability_weak_limit_nonnegative_support
import Theorems.Thm_AvramDividend_Classical_excursion_rescaled_probability_support_mass
import Theorems.Thm_AvramDividend_Classical_excursion_capped_laplace_tendsto_of_finite_weak
import Theorems.Thm_AvramDividend_Classical_excursion_laplace_lintegral_eq_on_supported_measure
import Theorems.Thm_AvramDividend_Classical_excursion_lintegral_limit_of_strict_subsequence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

/-!
Direct fixed-mass Prokhorov construction and Laplace-transform limit,
using only already Proved published helpers; this compact alternative
does not await registration of the composite subsequence helper.
-/
theorem solution
    (β : ℕ → Measure ℝ) (k : ℝ) (hk : 0 < k) (F : ℝ → ℝ)
    (hFpos : ∀ s : ℝ, 0 ≤ s → 0 < F s)
    (hmass : ∀ n : ℕ, β n univ = ENNReal.ofReal (k⁻¹))
    (hsupport : ∀ n : ℕ, β n (Iio (0 : ℝ)) = 0)
    (htight : IsTightMeasureSet (Set.range β))
    (hconv : ∀ s : ℝ, 0 ≤ s → Tendsto (fun n : ℕ =>
      ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂β n) atTop (𝓝 (ENNReal.ofReal ((F s)⁻¹)))) :
    ∃ μ : Measure ℝ, μ (Iio (0 : ℝ)) = 0 ∧ μ univ = ENNReal.ofReal (k⁻¹) ∧
      (∀ s : ℝ, 0 ≤ s → (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) =
        ENNReal.ofReal ((F s)⁻¹)) := by
  let c : NNReal := ⟨k⁻¹, le_of_lt (inv_pos.mpr hk)⟩
  have hc : (0 : NNReal) < c := by
    change (0 : ℝ) < k⁻¹
    exact inv_pos.mpr hk
  have hce : (c : ENNReal) = ENNReal.ofReal (k⁻¹) := by
    rw [show (k⁻¹ : ℝ) = (c : ℝ) from rfl, ENNReal.ofReal_coe_nnreal]
  obtain ⟨ν, hν, hνmass⟩ := AvramDividend.Classical.excursion_fixed_mass_finite_measure_family
    β c (fun n => by simpa only [hce] using hmass n)
  have hnz (n : ℕ) : ν n ≠ 0 := by
    intro hz
    have hm : (ν n).mass = 0 := by simp [hz]
    exact (ne_of_gt hc) ((hνmass n).symm.trans hm)
  have htightν : IsTightMeasureSet (Set.range (fun n : ℕ => (ν n : Measure ℝ))) := by
    have heq : (fun n : ℕ => (ν n : Measure ℝ)) = β := by
      funext n
      exact hν n
    simpa only [heq] using htight
  obtain ⟨P, φ, hφ, hlim⟩ :=
    AvramDividend.Classical.excursion_fixed_mass_normalized_prokhorov_subsequence
      ν c hc hνmass hnz htightν
  have hPsup : (P : Measure ℝ) (Iio (0 : ℝ)) = 0 := by
    apply AvramDividend.Classical.excursion_probability_weak_limit_nonnegative_support
      (fun n => (ν (φ n)).normalize) P hlim
    intro n
    apply (ProbabilityMeasure.null_iff_toMeasure_null _ _).mp
    apply AvramDividend.Classical.excursion_finite_measure_normalize_nonnegative_support
      (ν (φ n)) (hnz (φ n))
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    simpa only [hν (φ n)] using hsupport (φ n)
  let μf : FiniteMeasure ℝ := c • P.toFiniteMeasure
  let μ : Measure ℝ := μf
  obtain ⟨hμsup, hμmass⟩ := AvramDividend.Classical.excursion_rescaled_probability_support_mass P c hPsup
  have hlimfin : Tendsto (fun n : ℕ => ν (φ n)) atTop (𝓝 μf) :=
    AvramDividend.Classical.excursion_rescale_normalized_weak_limit ν c hνmass P φ hlim
  refine ⟨μ, hμsup, hμmass.trans hce, ?_⟩
  intro s hs
  have hcap := AvramDividend.Classical.excursion_capped_laplace_tendsto_of_finite_weak
    (fun n => ν (φ n)) μf hlimfin s hs
  have hcapβ : Tendsto (fun n : ℕ =>
      ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂β (φ n))
      atTop (𝓝 (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂μ)) := by
    simpa only [μ, hν] using hcap
  have hsrc (n : ℕ) :=
    AvramDividend.Classical.excursion_laplace_lintegral_eq_on_supported_measure
      (β (φ n)) s (hsupport (φ n))
  have hdst :=
    AvramDividend.Classical.excursion_laplace_lintegral_eq_on_supported_measure μ s hμsup
  have hsub : Tendsto (fun n : ℕ =>
      ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂β (φ n))
      atTop (𝓝 (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ)) := by
    simpa only [hsrc, hdst] using hcapβ
  exact AvramDividend.Classical.excursion_lintegral_limit_of_strict_subsequence
    β μ (fun x : ℝ => ENNReal.ofReal (Real.exp (-(s * x))))
    φ hφ (ENNReal.ofReal ((F s)⁻¹)) (hconv s hs) hsub
