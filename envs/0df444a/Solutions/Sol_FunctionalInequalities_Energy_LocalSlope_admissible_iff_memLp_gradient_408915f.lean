-- Prove2me | solution 1 for FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:53:00.588231+00:00
-- url     : https://prove2.me/submissions/e837139a-bfdb-4551-adeb-95c6d17e1801

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_eq_norm_gradient_408915f

noncomputable section
open MeasureTheory Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [sct : SecondCountableTopology E]
  [FiniteDimensional ℝ E] (ν : ProbabilityMeasure E) (m : Measure E)
  [Measure.IsAddHaarMeasure m]
omit sct in
/-- Step 2: Rademacher and absolute continuity identify the two pointwise energies almost
everywhere for locally Lipschitz tests, with no integrability or density lower bound premise. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_ae_eq_norm_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    (fun x ↦ apply f x) =ᵐ[(ν : Measure E)]
      (fun x ↦ ENNReal.ofReal ‖gradient f x‖) := by
  filter_upwards [hν.ae_le
    (Energy.Euclidean.LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hf m)]
    with x hx
  exact apply_eq_norm_gradient_408915f f x hx
omit sct in
/-- Step 3: equality of the extended local-slope and gradient energies, also when infinite.
The lintegral keeps nonintegrable functions from acquiring a spurious zero energy. -/
theorem FunctionalInequalities.Energy.LocalSlope.energy_eq_lintegral_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    energy ν f = ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E) := by
  unfold energy
  apply lintegral_congr_ae
  filter_upwards [apply_ae_eq_norm_gradient ν m hν f hf] with x hx
  rw [hx]
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities.Energy.LocalSlope in
/-- Step 4: the exact existing literature test domain, expressed by L2 gradient membership.
This is a theorem about the existing definition, not an additional admissibility assumption. -/
theorem solution (hν : (ν : Measure E) ≪ m) (f : E → ℝ) :
    FunctionalInequalities.Energy.LocalSlope.Admissible ν f ↔
      LocallyLipschitz f ∧ MemLp f 2 (ν : Measure E) ∧ MemLp (gradient f) 2 (ν : Measure E) := by
  have hmem : MemLp (gradient f) 2 (ν : Measure E) ↔
      (∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E)) ≠ ⊤ := by
    rw [MemLp, and_iff_right
      (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.aestronglyMeasurable_gradient f _)]
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    simp [← ofReal_norm, lt_top_iff_ne_top]
  constructor
  · intro h
    refine ⟨h.locallyLipschitz, h.memLp_two, hmem.mpr ?_⟩
    rw [← FunctionalInequalities.Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν f h.locallyLipschitz]
    exact h.finite_energy
  · rintro ⟨hlip, hL2, hgrad⟩
    refine ⟨hlip, hL2, ?_⟩
    rw [FunctionalInequalities.Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν f hlip]
    exact hmem.mp hgrad
