-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_arbitrary_weight_full_stieltjes_control_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:40:32.279986+00:00
-- url     : https://prove2.me/submissions/fe22e8d3-ff44-4900-8ba5-ec6cddf08bc0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_arbitrary_weight_right_atom_hjump_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The full source Stieltjes reward is controlled on the support of an arbitrary
nonnegative payoff weight by actual chronological jump secants and the diffuse gradient. -/
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
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hjump : ∀ t : ℝ≥0, t ≤ T → f (t : ℝ) ≠ 0 →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s : ℝ, f s ∂μ) ≤
      (∑' s : A,
        ENNReal.ofReal
          (w (riskProcess X x D (s : ℝ).toNNReal ω) -
            w (riskProcess X x D (s : ℝ).toNNReal ω -
              (rightLimit D (s : ℝ).toNNReal ω -
                D (s : ℝ).toNNReal ω))) * f (s : ℝ)) +
      (∫⁻ s : ℝ,
        f s * ENNReal.ofReal
          (deriv w (riskProcess X x D s.toNNReal ω)) ∂μdiffuse) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  let j : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal
      (w (riskProcess X x D s.toNNReal ω) -
        w (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω)))
  let g : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
  obtain ⟨A, μatom, μdiffuse, hAcount, hAmeas,
    hdecomp, hsum, hsupport, hnull, hReward⟩ :=
    avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split D hD ω T f
  have hAll :
      (∫⁻ s : ℝ, f s ∂μ) =
        (∑' s : A, μ {(s : ℝ)} * f (s : ℝ)) +
          (∫⁻ s : ℝ, f s ∂μdiffuse) := by
    change (∫⁻ s : ℝ, f s ∂μ) =
      (∑' s : A, μ {(s : ℝ)} * f (s : ℝ)) +
        (∫⁻ s : ℝ, f s ∂μdiffuse) at hReward
    exact hReward
  have hAtom :
      (∑' s : A, μ {(s : ℝ)} * f (s : ℝ)) ≤
        (∑' s : A, j (s : ℝ) * f (s : ℝ)) := by
    simpa only [j] using
      (avram_wave4_04b_arbitrary_weight_right_atom_hjump_bound
        X x D hD w ω T f hjump A)
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
  have hDiff :
      (∫⁻ s : ℝ, f s ∂μdiffuse) ≤
        (∫⁻ s : ℝ, f s * g s ∂μdiffuse) := by
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
      have hGE : (1 : ℝ≥0∞) ≤ g s := by
        change (1 : ℝ≥0∞) ≤
          ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
        simpa using (ENNReal.ofReal_le_ofReal hG)
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hGE (by positivity))
  refine ⟨A, μatom, μdiffuse, hAcount, hAmeas, hdecomp, hnull, ?_⟩
  change (∫⁻ s : ℝ, f s ∂μ) ≤
    (∑' s : A, j (s : ℝ) * f (s : ℝ)) +
      (∫⁻ s : ℝ, f s * g s ∂μdiffuse)
  calc
    (∫⁻ s : ℝ, f s ∂μ) =
        (∑' s : A, μ {(s : ℝ)} * f (s : ℝ)) +
          (∫⁻ s : ℝ, f s ∂μdiffuse) := hAll
    _ ≤ (∑' s : A, j (s : ℝ) * f (s : ℝ)) +
          (∫⁻ s : ℝ, f s * g s ∂μdiffuse) :=
      add_le_add hAtom hDiff
