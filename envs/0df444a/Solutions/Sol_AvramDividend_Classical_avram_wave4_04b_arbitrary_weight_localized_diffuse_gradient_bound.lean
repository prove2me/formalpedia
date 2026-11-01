-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_arbitrary_weight_localized_diffuse_gradient_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:36:05.369573+00:00
-- url     : https://prove2.me/submissions/ec603b3a-1b2d-49f8-b387-bbf6ee025f77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The entire atomless source Stieltjes reward is controlled by the interior
gradient wherever the nonnegative payoff weight is nonzero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞)
    (hloc : ∀ t : ℝ≥0, t ≤ T → f (t : ℝ) ≠ 0 →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s : ℝ, f s ∂μdiffuse) ≤
      (∫⁻ s : ℝ,
        f s * ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
          ∂μdiffuse) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  obtain ⟨A, μatom, μdiffuse, hAcount, hAmeas, hdecomp,
    hsum, hsupport, hnull, _, _⟩ :=
    avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse D hD ω T
  have hRestrictedZero :
      μ (Icc (0 : ℝ) (T : ℝ))ᶜ = 0 := by
    simp [μ]
  have hMeasureLe : μdiffuse ≤ μ := by
    exact (Measure.le_add_left le_rfl).trans (le_of_eq hdecomp.symm)
  have hDiffOutside :
      μdiffuse (Icc (0 : ℝ) (T : ℝ))ᶜ = 0 := by
    apply le_antisymm
    · calc
        μdiffuse (Icc (0 : ℝ) (T : ℝ))ᶜ ≤
            μ (Icc (0 : ℝ) (T : ℝ))ᶜ := hMeasureLe _
        _ = 0 := hRestrictedZero
    · exact bot_le
  have hAE :
      ∀ᵐ s ∂μdiffuse, s ∈ Icc (0 : ℝ) (T : ℝ) := by
    apply ae_iff.mpr
    change μdiffuse (Icc (0 : ℝ) (T : ℝ))ᶜ = 0
    exact hDiffOutside
  refine ⟨A, μatom, μdiffuse, hAcount, hAmeas,
    hdecomp, hsum, hsupport, hnull, ?_⟩
  apply lintegral_mono_ae
  filter_upwards [hAE] with s hs
  by_cases hf : f s = 0
  · simp [hf]
  · have hcoe : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.1
    have ht : s.toNNReal ≤ T := by
      exact_mod_cast (show ((s.toNNReal : ℝ) ≤ (T : ℝ)) from by
        simpa only [hcoe] using hs.2)
    have hloc' :=
      hloc s.toNNReal ht (by simpa only [hcoe] using hf)
    have hG : 1 ≤ deriv w (riskProcess X x D s.toNNReal ω) :=
      hw_grad _ hloc'.1 hloc'.2
    have hGE :
        (1 : ℝ≥0∞) ≤ ENNReal.ofReal
          (deriv w (riskProcess X x D s.toNNReal ω)) := by
      simpa using (ENNReal.ofReal_le_ofReal hG)
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hGE (by positivity))
