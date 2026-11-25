-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GroupGeneratedByExp.trotterMx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:11:54.639795+00:00
-- url     : https://prove2.me/submissions/8b293d57-e5e0-4f77-b719-8457330a588f

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Theorems.Thm_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_trotter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Formalism.FourierDecayAlt.P.GroupGeneratedByExp
namespace Formalism.FourierDecayAlt.P.GroupGeneratedByExp
theorem _root_.solution (N : ℕ) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    Tendsto (fun n : ℕ => (NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • X) * NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y))) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin N) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℂ)
  have hc : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℝ _
  have h := trotter X Y
  simp only [Complex.coe_smul]
  exact h
end Formalism.FourierDecayAlt.P.GroupGeneratedByExp
