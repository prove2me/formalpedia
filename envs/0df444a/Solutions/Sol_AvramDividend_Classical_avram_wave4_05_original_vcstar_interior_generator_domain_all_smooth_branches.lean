-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_original_vcstar_interior_generator_domain_all_smooth_branches
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:55:27.861321+00:00
-- url     : https://prove2.me/submissions/dae579b0-43cf-4d42-abb1-3f7f794b4b21

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_standing_nonzero_scale_normaliser
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_integrable_of_nonzero_factor
import Theorems.Thm_AvramDividend_Classical_levy_generatorIntegrable_const_mul
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_congr_scaledW_inside_cstar
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The entire original three-way smoothness alternative gives true local Lévy-generator domain. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x := by
  let d := scaleDeriv W (cstar W).toReal
  have hk : divE (1 : ℝ) d ≠ 0 := by
    exact avram_wave4_05_standing_nonzero_scale_normaliser X hX q hq W hW hc
  have hWdomain := scaleFunction_generator_integrable_of_nonzero_factor
    X hX q hq W hW h_smooth hc hk
  have hscaled : (fun z : ℝ => divE (W z) d) =
      (fun z : ℝ => divE (1 : ℝ) d * W z) := by
    funext z
    by_cases hd : d = ⊤
    · simp [divE, hd]
    · simp [divE, hd, div_eq_mul_inv, mul_comm]
  intro x hx
  have hmul : X.GeneratorIntegrable
      (fun z : ℝ => divE (1 : ℝ) d * W z) x :=
    levy_generatorIntegrable_const_mul X W (divE 1 d) x (hWdomain x hx)
  have htarget := (vcstar_generator_congr_scaledW_inside_cstar X q W hW x hx).1
  apply htarget.mpr
  rw [hscaled]
  exact hmul
