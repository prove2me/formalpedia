-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.K_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:26:15.024844+00:00
-- url     : https://prove2.me/submissions/d54b2bbd-d513-400b-9c77-d9e819bebf4a

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
theorem _root_.solution (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) :
    Vᴴ * H = (Vᴴ * H * V) * prj H V := by
  have h := Matrix.mul_nonsing_inv _ hΓ
  have e : (Vᴴ * H * V) * prj H V = ((Vᴴ * H * V) * (Vᴴ * H * V)⁻¹) * (Vᴴ * H) := by
    simp only [prj, Matrix.mul_assoc]
  rw [e, h, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.HermitianProjections
