-- Prove2me | solution 1 for FunctionalInequalities.Probability.integrable_exp_sub_norm_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:27:40.794002+00:00
-- url     : https://prove2.me/submissions/785a99ad-cc64-4687-8d79-4c6b5fcc8ec7

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- Actual exponential norm decay is Haar-integrable in every finite dimension.
The nontrivial case uses polar integration; the zero-dimensional case is compact. -/
theorem solution [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (dx : Measure E) [dx.IsAddHaarMeasure] {c : ℝ} (hc : 0 < c) (M : ℝ) :
    Integrable (fun y : E => Real.exp (M - c * ‖y‖)) dx := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let := hE
    have : CompactSpace E := inferInstance
    have : IsFiniteMeasure dx := inferInstance
    have heq : (fun y : E => Real.exp (M - c * ‖y‖)) = fun _ : E => Real.exp M := by
      funext y
      rw [Subsingleton.elim y 0]
      simp
    rw [heq]
    exact integrable_const _
  · let := hE
    have hi : Integrable (fun y : E => Real.exp (-c * ‖y‖)) dx := by
      apply (integrable_fun_norm_addHaar dx (f := fun t : ℝ => Real.exp (-c * t))).mpr
      simpa only [smul_eq_mul, Real.rpow_natCast, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) (p := 1)
          (by have hsn := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E - 1); linarith) (by norm_num) hc)
    convert hi.const_mul (Real.exp M) using 1
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
