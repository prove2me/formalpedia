-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_admissible_full_signed_generator_stieltjes_budget_without_hjump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:25:48.601168+00:00
-- url     : https://prove2.me/submissions/0c654cf8-4cd8-4458-a35f-b4ee5796cf9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_and_local_physical_generator_full_stieltjes_HJB_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- On the original BV source, the signed physical generator and Stieltjes HJB integral budget requires no independent right-dividend hjump hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (F : (ℝ≥0 × Ω) → ℝ)
    (hF : ∀ p ∈ E, F p =
      Real.exp (-(q * (p.1 : ℝ))) *
      (X.generator w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1)))
    (hFI : IntegrableOn F E μ)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hIDiv : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω)) :
    (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∫ p in E, F p ∂μ) +
      (∫ t in A, Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω))
        ∂(dividendMeasure D ω)) ≤ w x := by
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hJump :=
    avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
      X hX hBV C hC w hw_cont hw_smooth hw_grad
      x hx hxc D hD
  exact
    avram_wave7_02_original_BV_initial_atom_and_local_physical_generator_full_stieltjes_HJB_budget
      X hBV q w C hw_gen hw_grad
      x D hStrat hJump ω μ E hEm hEregion
      F hF hFI A hAm hAregion hIDiv
