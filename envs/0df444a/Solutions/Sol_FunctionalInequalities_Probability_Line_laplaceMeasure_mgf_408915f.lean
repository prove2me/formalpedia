-- Prove2me | solution 1 for FunctionalInequalities.Probability.Line.laplaceMeasure_mgf_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:03:26.98732+00:00
-- url     : https://prove2.me/submissions/00e4a0de-3868-46d7-a848-806a9d6e28eb

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.MGFAnalytic
import Theorems.Thm_FunctionalInequalities_Probability_Line_integral_exp_mul_laplaceDensity_408915f

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Line
end FunctionalInequalities.Probability.Line
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Line
section Moments
open ProbabilityTheory Filter Set
open scoped Topology
namespace FunctionalInequalities.Probability.Line
end FunctionalInequalities.Probability.Line
open FunctionalInequalities.Probability.Line in
/-- The law-level moment generating function on `|w| < β`. -/
theorem solution {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    Integrable (fun s : ℝ => Real.exp (w * s)) (FunctionalInequalities.Probability.Line.laplaceMeasure β) ∧
      mgf id (FunctionalInequalities.Probability.Line.laplaceMeasure β) w = β ^ 2 / (β ^ 2 - w ^ 2) := by
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (FunctionalInequalities.Probability.Line.laplaceDensity β s)) := by
    unfold FunctionalInequalities.Probability.Line.laplaceDensity
    fun_prop
  have hfin : ∀ᵐ s : ℝ ∂volume, ENNReal.ofReal (FunctionalInequalities.Probability.Line.laplaceDensity β s) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hnn (s : ℝ) : 0 ≤ FunctionalInequalities.Probability.Line.laplaceDensity β s := by
    unfold FunctionalInequalities.Probability.Line.laplaceDensity
    positivity
  have h := FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity_408915f hβ hw
  constructor
  · unfold FunctionalInequalities.Probability.Line.laplaceMeasure
    rw [integrable_withDensity_iff hm hfin]
    simpa only [ENNReal.toReal_ofReal (hnn _)] using h.1
  · change (∫ s : ℝ, Real.exp (w * id s) ∂volume.withDensity
      (fun s => ENNReal.ofReal (FunctionalInequalities.Probability.Line.laplaceDensity β s))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hm hfin]
    simpa only [id_eq, ENNReal.toReal_ofReal (hnn _), smul_eq_mul, mul_comm] using h.2
