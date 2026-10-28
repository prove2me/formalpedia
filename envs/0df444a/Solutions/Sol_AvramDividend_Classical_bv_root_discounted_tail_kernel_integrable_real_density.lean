-- Prove2me | solution 1 for AvramDividend.Classical.bv_root_discounted_tail_kernel_integrable_real_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:04:38.741061+00:00
-- url     : https://prove2.me/submissions/1e08a73c-f34c-4da6-8fad-07876db8813c

import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_real_density_package
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.WithDensity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The finite BV Esscher density is Lebesgue integrable. -/
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
      Integrable K volume ∧
      κ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x)) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by
  obtain ⟨κ, K, hsf, hac, hsupp, hgap, hMeas, hPos, hDens, hLap⟩ :=
    bv_root_discounted_tail_kernel_real_density_package X hbv q hq φ hφ hroot hδ
  have hFin : HasFiniteIntegral K volume := by
    apply (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hPos)).2
    have hm : κ Set.univ < ⊤ := lt_trans hgap ENNReal.ofReal_lt_top
    rw [hDens] at hm
    simpa [withDensity_apply] using hm
  have hInt : Integrable K volume :=
    ⟨hMeas.aestronglyMeasurable, hFin⟩
  exact ⟨κ, K, hsf, hac, hsupp, hgap, hMeas, hPos,
    hInt, hDens, hLap⟩
