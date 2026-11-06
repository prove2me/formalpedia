-- Prove2me | solution 9 for AvramDividend.Classical.barrier_cstar_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:23:40.392628+00:00
-- url     : https://prove2.me/submissions/bd4ad18d-bdc4-489a-8e91-375bc09b793d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_verification_upper_bounds
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ x : ℝ, (cstar W).toReal < x →
          X.GeneratorIntegrable (vcstar W) x ∧
            X.generator (vcstar W) x - q * vcstar W x ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by
  have hc : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hUpper :=
    barrier_cstar_verification_upper_bounds X hX q hq W hW hc h_smooth
  refine ⟨hc, ?_, ?_⟩
  · intro x hx
    obtain ⟨hD, hValue⟩ :=
      barrier_cstar_attains_value_all_capital X hX q hq W hW hc x hx
    have hLower :=
      (avram_sweep16_barrier_cstar_lower_bounds_from_attainment
        X hX q hq W hW hc x hx).1
    exact ⟨hD, hValue, le_antisymm (hUpper.1 x hx) hLower⟩
  · intro hgen x hx
    obtain ⟨hD, _⟩ :=
      barrier_cstar_attains_value_all_capital X hX q hq W hW hc x hx
    have hLower :=
      (avram_sweep16_barrier_cstar_lower_bounds_from_attainment
        X hX q hq W hW hc x hx).2
    exact ⟨hD.1, le_antisymm (hUpper.2 hgen x hx) hLower⟩
