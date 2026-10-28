-- Prove2me | solution 1 for AvramDividend.Classical.bv_root_discounted_tail_kernel_real_density_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:56:48.019823+00:00
-- url     : https://prove2.me/submissions/92f7c68f-f0d7-4ebe-ae7c-e1dc0fc27665

import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_ac_package
import Theorems.Thm_AvramDividend_Classical_sigmaFinite_absolutelyContinuous_has_real_density
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The finite root-shifted BV Esscher jump-tail kernel has a real Lebesgue density. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hδ : 0 < X.drift) :
    ∃ (κ : Measure ℝ) (K : ℝ → ℝ),
      SFinite κ ∧ κ ≪ volume ∧ κ (Iio (0 : ℝ)) = 0 ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      Measurable K ∧ (∀ x : ℝ, 0 ≤ K x) ∧
      κ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x)) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by
  obtain ⟨κ, hsf, hac, hsupp, hgap, hLap⟩ :=
    bv_root_discounted_tail_kernel_ac_package X hbv q hq φ hφ hroot hδ
  haveI : IsFiniteMeasure κ := ⟨lt_trans hgap ENNReal.ofReal_lt_top⟩
  obtain ⟨K, hKmeas, hKpos, hKmeasure⟩ :=
    sigmaFinite_absolutelyContinuous_has_real_density κ hac
  exact ⟨κ, K, hsf, hac, hsupp, hgap,
    hKmeas, hKpos, hKmeasure, hLap⟩
