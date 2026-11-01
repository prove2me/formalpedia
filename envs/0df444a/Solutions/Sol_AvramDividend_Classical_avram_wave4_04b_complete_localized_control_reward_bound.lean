-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_complete_localized_control_reward_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:04:43.812129+00:00
-- url     : https://prove2.me/submissions/05409aa8-3fc2-4d80-8856-78f914f042d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_discounted_complete_stieltjes_atom_diffuse
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_discounted_right_atom_hjump_tsum_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (hloc : ∀ t : ℝ≥0, t ≤ T →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hjump : ∀ t : ℝ≥0, t ≤ T →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      (∑' s : A,
        ENNReal.ofReal
          (w (riskProcess X x D (s : ℝ).toNNReal ω) -
            w (riskProcess X x D (s : ℝ).toNNReal ω -
              (rightLimit D (s : ℝ).toNNReal ω -
                D (s : ℝ).toNNReal ω))) *
          ENNReal.ofReal (Real.exp (-(q * (s : ℝ))))) +
      (∫⁻ s : ℝ,
        ENNReal.ofReal (Real.exp (-(q * s))) *
          ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
            ∂μdiffuse) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-(q * s)))
  let j : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal
      (w (riskProcess X x D s.toNNReal ω) -
        w (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω)))
  let g : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
  obtain ⟨A, μatom, μdiffuse, hAcount, hAmeas,
    hdecomp, hsum, hsupport, hnull, hReward⟩ :=
    avram_wave4_04b_discounted_complete_stieltjes_atom_diffuse D hD ω T q
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
    simpa only [f, j] using
      (avram_wave4_04b_discounted_right_atom_hjump_tsum_bound
        X x D hD w ω T q hjump A)
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
    have hcoe : (s.toNNReal : ℝ) = s :=
      Real.coe_toNNReal s hs.1
    have ht : s.toNNReal ≤ T := by
      exact_mod_cast (show ((s.toNNReal : ℝ) ≤ (T : ℝ)) from by
        simpa only [hcoe] using hs.2)
    have hG : 1 ≤ deriv w (riskProcess X x D s.toNNReal ω) :=
      hw_grad _ (hloc s.toNNReal ht).1 (hloc s.toNNReal ht).2
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
