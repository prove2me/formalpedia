-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_continuousOn_Icc_below_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:59:13.012406+00:00
-- url     : https://prove2.me/submissions/8d9f530e-f5af-4b4b-b33d-bc71c1d7a913

import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal) :
    ContinuousOn (vcstar W) (Icc 0 (cstar W).toReal) := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 < a := hpos
  have hcontW : ContinuousOn W (Icc 0 a) :=
    hW.2.2.1.mono (by
      intro z hz
      exact hz.1)
  have hscaled : ContinuousOn
      (fun z : ℝ => (deriv W a)⁻¹ * W z) (Icc 0 a) :=
    continuousOn_const.mul hcontW
  have heq : EqOn
      (vcstar W)
      (fun z : ℝ => (deriv W a)⁻¹ * W z)
      (Icc 0 a) := by
    intro z hz
    have hza : z ≤ (cstar W).toReal := hz.2
    have hs := vcstar_eq_scaledW_le_cstar_of_support
      W hW.1 z hza
    have ha0 : a ≠ 0 := ne_of_gt ha
    rw [hs]
    simp [divE, scaleDeriv, ha0, a, div_eq_mul_inv, mul_comm]
  exact hscaled.congr heq