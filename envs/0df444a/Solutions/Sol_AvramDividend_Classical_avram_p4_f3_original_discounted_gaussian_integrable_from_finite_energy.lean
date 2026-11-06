-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_integrable_from_finite_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:26:38.466603+00:00
-- url     : https://prove2.me/submissions/5affb50e-beb2-4884-be65-074037756d5d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_physical_gaussian_finite_joint_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual discounted Gaussian original-process source coefficient has finite L1 under physical finite measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤)
    (hGm : AEStronglyMeasurable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
           if y ∈ Icc δ K then y else δ))) μ) :
    Integrable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
           if y ∈ Icc δ K then y else δ))) μ := by
  let G : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
           if y ∈ Icc δ K then y else δ)))
  have hG2 : (∫⁻ p, ENNReal.ofReal ((G p) ^ 2) ∂μ) < ⊤ := by
    simpa [G] using
      (avram_p4_f3_original_discounted_physical_gaussian_finite_joint_energy
        X x D w C hw_cont hw_neg hw_smooth q hq δ K ε
        hδ hδK hK hε μ hμ)
  have hG2I : Integrable (fun p => (G p) ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hGm.pow 2)
      (Filter.Eventually.of_forall (fun p => sq_nonneg (G p)))).mp
      (ne_of_lt hG2)
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  have hGL2 : MemLp G 2 μ := (memLp_two_iff_integrable_sq hGm).2 hG2I
  simpa [G] using hGL2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
