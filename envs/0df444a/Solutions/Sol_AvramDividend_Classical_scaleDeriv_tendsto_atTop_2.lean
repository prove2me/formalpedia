-- Prove2me | solution 2 for AvramDividend.Classical.scaleDeriv_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T23:07:30.354047+00:00
-- url     : https://prove2.me/submissions/af00db2d-1fc1-41e0-ae48-6298b72b9504
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_eventually_ge_exp

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto (deriv W) atTop atTop := by
  obtain ⟨φ, c, hφ, hc, hdom⟩ :=
    scaleDeriv_eventually_ge_exp X hX q hq W hW
  have hφx : Tendsto (fun x : ℝ => φ * x) atTop atTop :=
    tendsto_id.const_mul_atTop hφ
  have hlow : Tendsto (fun x : ℝ => c * Real.exp (φ * x)) atTop atTop := by
    exact (Real.tendsto_exp_atTop.comp hφx).const_mul_atTop hc
  exact tendsto_atTop_mono' atTop hdom hlow
