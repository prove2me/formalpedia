-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.prj_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:26:16.847551+00:00
-- url     : https://prove2.me/submissions/198d0d99-111c-4da1-a614-060d8b6a7cc8

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (x : n → ℂ) (hx : (Vᴴ * H) *ᵥ x = 0) :
    prj H V *ᵥ x = 0 := by
  have e : prj H V = (Vᴴ * H * V)⁻¹ * (Vᴴ * H) := by
    simp only [prj, Matrix.mul_assoc]
  rw [e, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
end Formalism.FourierDecayAlt.P.HermitianProjections
