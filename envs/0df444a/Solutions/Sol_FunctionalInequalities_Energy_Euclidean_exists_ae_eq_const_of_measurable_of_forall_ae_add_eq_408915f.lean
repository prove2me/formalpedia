-- Prove2me | solution 1 for FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:51:59.677407+00:00
-- url     : https://prove2.me/submissions/fba60b8f-5e60-4c2d-846b-808e25d43fe0

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : Measure V) [m.IsAddHaarMeasure]
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities.Energy.Euclidean in
/-- A measurable function invariant under every translation up to null sets is almost everywhere
constant. -/
theorem solution {g : V → ℝ} (hg : Measurable g)
    (htr : ∀ v : V, ∀ᵐ x ∂m, g (x + v) = g x) :
    ∃ c : ℝ, ∀ᵐ x ∂m, g x = c := by
  have hmeas :
      MeasurableSet {q : V × V | g (q.2 + q.1) = g q.2} := by
    exact measurableSet_eq_fun
      (hg.comp (measurable_snd.add measurable_fst))
      (hg.comp measurable_snd)

  have hprod : ∀ᵐ v ∂m, ∀ᵐ y ∂m, g (y + v) = g y := by
    filter_upwards [] with v
    exact htr v

  have hcomm : ∀ᵐ y ∂m, ∀ᵐ v ∂m, g (y + v) = g y :=
    (Measure.ae_ae_comm (μ := m) (ν := m) hmeas).mp hprod

  have hm0 : m ≠ 0 := NeZero.ne m
  have hne : (ae m).NeBot := ae_neBot.2 hm0
  obtain ⟨y₀, hy₀⟩ := Filter.Eventually.exists hcomm

  have hpull : ∀ᵐ z ∂m, g (y₀ + (z - y₀)) = g y₀ :=
    (measurePreserving_sub_right m y₀).quasiMeasurePreserving.ae hy₀

  refine ⟨g y₀, ?_⟩
  filter_upwards [hpull] with z hz
  have hEq : y₀ + (z - y₀) = z := by
    abel
  rw [hEq] at hz
  exact hz
