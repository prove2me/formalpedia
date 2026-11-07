-- Prove2me | solution 4 for AvramDividend.Classical.avram_p3_grid4_original_single_signed_strict_source_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:27:14.225793+00:00
-- url     : https://prove2.me/submissions/6167a252-823a-4609-865a-bae22bdce9c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_physical_stopped_cell_error_witness
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_stopped_grid_signed_source_mean
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_natural_inner_clock_delta_certificate
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep14_original_BV_vanishing_error_strict_mean
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- Original finite-grid signed HJB compensation, passed through the exact
   strict-prefix stochastic cash and surviving terminal limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ Z : Ω → ℝ,
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ≤ w x + Z ω) := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let v : ℕ → ℝ := fun n => T - δ n
  rcases avram_bv_strict6_natural_inner_clock_delta_certificate T hTpos with
    ⟨hδpos, hδle, hδanti, hδtendsto⟩
  rcases avram_p3_grid4_original_physical_stopped_cell_error_witness
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hTpos with
    ⟨u, M, B, Err, hgrid, hmono, hB, hMI, hErrInt, hErrMean, hPhysical⟩
  have hvmono : Monotone v := by
    intro a b hab
    exact sub_le_sub_left (hδanti hab) T
  have hvnonneg : ∀ n, 0 ≤ v n := by
    intro n
    exact sub_nonneg.mpr (hδle n)
  have hvbelow : ∀ n, v n ≤ T := by
    intro n
    exact sub_le_self T (le_of_lt (hδpos n))
  have hvlim : Tendsto v atTop (𝓝 T) := by
    simpa [v, δ] using (tendsto_const_nhds.sub hδtendsto)
  have hvcover : ∀ s : ℝ, s < T → ∃ n, s < v n := by
    intro s hs
    exact (hvlim.eventually (isOpen_Ioi.mem_nhds hs)).exists
  have hSigned (n : ℕ) :
      Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0 := by
    rcases hMI n with ⟨hMint, hMzero, hBint⟩
    exact avram_bv_strict6_original_stopped_grid_signed_source_mean
      X hBV q w C hw_gen hw_grad x D u hmono n (M n) (B n)
      (hB n) hMint hBint hMzero
  let S : ℝ≥0 := ⟨T, hT⟩
  have hPhysicalV (n : ℕ) : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (v n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := by
    simpa [v, δ] using hPhysical n
  have hBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ∂P) ≤ w x := by
    exact avram_integration_sweep14_original_BV_vanishing_error_strict_mean
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      S v hvmono hvnonneg hvbelow hvcover M B Err
      hSigned hErrInt hErrMean hPhysicalV
  exact avram_p3_bv_original_source_witness_from_strict_mean
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT hBudget
