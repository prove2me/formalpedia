-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_clipped_hjb_discounted_generator_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:32:23.490066+00:00
-- url     : https://prove2.me/submissions/5fdb7e87-a557-441f-9a40-d2a24f370896

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Same-source clipped HJB generator remainder is nonpositive at every physical time-path point. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    ∀ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.generator w (U p) - q * w (U p)) ≤ 0 := by
  dsimp only
  intro p
  let y := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  have hlo : δ ≤ (if y ∈ Icc δ K then y else δ) := by
    split_ifs with hy
    · exact hy.1
    · exact le_rfl
  have hhi : (if y ∈ Icc δ K then y else δ) ≤ K := by
    split_ifs with hy
    · exact hy.2
    · exact hδK
  have hpos : 0 < (if y ∈ Icc δ K then y else δ) :=
    lt_of_lt_of_le hδ hlo
  have hcap : ENNReal.ofReal (if y ∈ Icc δ K then y else δ) < C :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hhi) hK
  have hsign := (hw_gen (if y ∈ Icc δ K then y else δ) hpos hcap).2
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hsign
