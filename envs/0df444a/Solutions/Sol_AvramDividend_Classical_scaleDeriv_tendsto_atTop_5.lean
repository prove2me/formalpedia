-- Prove2me | solution 5 for AvramDividend.Classical.scaleDeriv_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-18T18:51:29.048428+00:00
-- url     : https://prove2.me/submissions/2e458df1-12b1-40d7-b6d3-f72ce9dbdf2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_eventually_ge_exp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Elementary analytic core: any function eventually bounded below by
    a positive exponential with a positive exponent tends to +infinity.
    This lemma has no assumptions about Lévy processes. -/
private theorem exponential_lower_bound_tendsto_atTop
    (f : ℝ → ℝ) (φ c : ℝ) (hφ : 0 < φ) (hc : 0 < c)
    (hbound : ∀ᶠ x in atTop, c * Real.exp (φ * x) ≤ f x) :
    Tendsto f atTop atTop := by
  have hphi : Tendsto (fun x : ℝ => φ * x) atTop atTop := by
    have h := (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).atTop_mul_const hφ
    simpa only [id_eq, mul_comm] using h
  have hexp : Tendsto (fun x : ℝ => Real.exp (φ * x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hphi
  have hscaled : Tendsto (fun x : ℝ => c * Real.exp (φ * x)) atTop atTop := by
    have h := hexp.atTop_mul_const hc
    simpa only [id_eq, mul_comm] using h
  exact tendsto_atTop_mono' atTop hbound hscaled

/-- Published scaleDeriv_tendsto_atTop reduction. This requires the
    still-Open scaleDeriv_eventually_ge_exp theorem to be Proved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto (deriv W) atTop atTop := by
  obtain ⟨φ, c, hφ, hc, hbound⟩ :=
    scaleDeriv_eventually_ge_exp X hX q hq W hW
  exact exponential_lower_bound_tendsto_atTop
    (deriv W) φ c hφ hc hbound
