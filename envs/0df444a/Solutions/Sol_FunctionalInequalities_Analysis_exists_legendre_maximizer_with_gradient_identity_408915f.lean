-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:19:14.871794+00:00
-- url     : https://prove2.me/submissions/5489be1c-bf35-427b-82b4-15fb0059cec0

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_conjugate_maximizer_eq_gradient_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_finite_maximum_of_upperSemicontinuous_linear_decay_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_tiltedObjective_data_408915f

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section Attainment
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Every interior point of the actual finite Legendre domain has an actual
primal maximizer. If the real-valued dual is differentiable there, the same
maximizer is its actual gradient. -/
theorem solution
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤}) :
    ∃ z : E,
      (inner ℝ z y : EReal) - φ z = FunctionalInequalities.Analysis.legendre φ y ∧
      (DifferentiableAt ℝ (fun q : E => (FunctionalInequalities.Analysis.legendre φ q).toReal) y →
        z = gradient (fun q : E => (FunctionalInequalities.Analysis.legendre φ q).toReal) y) := by
    rcases FunctionalInequalities.Analysis.tiltedObjective_data_408915f φ hφ hlsc y hy with
      ⟨husc, hnotTop, hfinite, a, b, ha, hdecay⟩
    rcases FunctionalInequalities.Analysis.exists_finite_maximum_of_upperSemicontinuous_linear_decay_408915f
        (fun x : E => (inner ℝ x y : EReal) - φ x)
        husc hnotTop hfinite a b ha hdecay with
      ⟨z, hzbot, hztop, hmax⟩
    have hle :
        (inner ℝ z y : EReal) - φ z ≤ FunctionalInequalities.Analysis.legendre φ y := by
      change
        (inner ℝ z y : EReal) - φ z ≤
          ⨆ x : E, (inner ℝ x y : EReal) - φ x
      exact le_iSup (fun x : E => (inner ℝ x y : EReal) - φ x) z
    have hge :
        FunctionalInequalities.Analysis.legendre φ y ≤ (inner ℝ z y : EReal) - φ z := by
      change
        (⨆ x : E, (inner ℝ x y : EReal) - φ x) ≤
          (inner ℝ z y : EReal) - φ z
      exact iSup_le (fun x => hmax x)
    have heq :
        (inner ℝ z y : EReal) - φ z = FunctionalInequalities.Analysis.legendre φ y :=
      le_antisymm hle hge
    refine ⟨z, heq, ?_⟩
    intro hd
    exact
      FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient_408915f
        φ hφ hy hd z heq
