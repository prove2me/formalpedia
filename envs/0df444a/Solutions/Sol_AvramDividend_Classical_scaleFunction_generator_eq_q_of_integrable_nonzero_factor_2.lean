-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_integrable_nonzero_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:17:51.84807+00:00
-- url     : https://prove2.me/submissions/b5319568-1104-486a-b225-6798915ee542
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_below_cstar_of_vcstar
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_generatorIntegrable


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hint : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0 := by
  have hsmoothW :
      0 < X.σ ∨ X.BoundedVariation ∨
        ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) := by
    rcases h_smooth with hσ | hs
    · exact Or.inl hσ
    · rcases hs with hbv | hvc
      · exact Or.inr (Or.inl hbv)
      · exact Or.inr (Or.inr
          (scaleFunction_contDiff_two_below_cstar_of_vcstar W hvc hk))
  by_cases htop : cstar W = ⊤
  · intro x hx
    have hxlt : x < 0 := by
      simpa [htop] using hx.2
    exact (not_lt_of_ge hx.1.le hxlt).elim
  · have ha : 0 < (cstar W).toReal :=
      ENNReal.toReal_pos (ne_of_gt hc) htop
    exact scaleFunction_generator_eq_q_of_generatorIntegrable
      X hX q hq W hW (cstar W).toReal ha hsmoothW hint
