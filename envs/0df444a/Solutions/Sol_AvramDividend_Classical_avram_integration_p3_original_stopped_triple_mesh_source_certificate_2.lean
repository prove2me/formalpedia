-- Prove2me | solution 2 for AvramDividend.Classical.avram_integration_p3_original_stopped_triple_mesh_source_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:02:30.913958+00:00
-- url     : https://prove2.me/submissions/5aac779d-906d-4b75-928d-59eb95fac6ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_original_stopped_signed_single_residual_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let Y : Ω → ℝ := fun ω =>
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0)
    ∃ Ymesh Mmesh Bmesh : ℕ → Ω → ℝ,
      ∃ M B DM DB : Ω → ℝ,
        (∀ n, AEStronglyMeasurable (Mmesh n) P) ∧
        (∀ n, AEStronglyMeasurable (Bmesh n) P) ∧
        Integrable DM P ∧ Integrable DB P ∧
        (∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω) ∧
        (∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω))) ∧
        (∀ n, (∫ ω, Mmesh n ω ∂P) = 0) ∧
        (∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0) ∧
        (∀ᵐ ω ∂P, ∀ n, Ymesh n ω ≤ w x + Mmesh n ω + Bmesh n ω) := by
  classical
  obtain ⟨Ymesh, Zmesh, Z, DZ, hMeas, hDZ, hDom,
    hYlim, hZlim, hMean, hBudget⟩ :=
    avram_a19_original_stopped_signed_single_residual_mesh
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  refine ⟨Ymesh, (fun _ _ => 0), Zmesh, (fun _ => 0), Z,
    (fun _ => 0), DZ, ?_, hMeas, ?_, hDZ, ?_, hDom,
    hYlim, ?_, hZlim, ?_, hMean, ?_⟩
  · intro n
    exact aestronglyMeasurable_const
  · exact integrable_zero _ _ _
  · intro n
    filter_upwards [] with ω
    simp
  · filter_upwards [] with ω
    exact tendsto_const_nhds
  · intro n
    simp
  · filter_upwards [hBudget] with ω hω
    intro n
    simpa using hω n
