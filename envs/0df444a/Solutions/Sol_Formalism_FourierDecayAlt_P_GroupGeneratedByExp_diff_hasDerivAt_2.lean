-- Prove2me | solution 2 for Formalism.FourierDecayAlt.P.GroupGeneratedByExp.diff_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T03:08:42.629595+00:00
-- url     : https://prove2.me/submissions/5abc772c-1a57-41b0-bc7c-0b91619c28b9

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Formalism.FourierDecayAlt.P.GroupGeneratedByExp
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The product `exp (t • X) * exp (t • Y)` and `exp (t • (X + Y))` agree to first order at `0`:
their difference has derivative `X + Y - (X + Y) = 0` there. -/
theorem solution (X Y : 𝔸) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) -
      NormedSpace.exp (t • (X + Y))) 0 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X + Y) (0 : ℝ)
  have h := (h1.mul h2).sub h3
  have e : (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) -
      NormedSpace.exp (t • (X + Y)))
      = ((fun u : ℝ => NormedSpace.exp (u • X)) * fun u : ℝ => NormedSpace.exp (u • Y))
        - fun u : ℝ => NormedSpace.exp (u • (X + Y)) := by
    funext t; simp [Pi.mul_apply, Pi.sub_apply]
  rw [e]
  simpa using h
