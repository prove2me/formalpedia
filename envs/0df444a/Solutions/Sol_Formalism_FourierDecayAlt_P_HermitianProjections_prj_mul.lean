-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.prj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:23:03.834648+00:00
-- url     : https://prove2.me/submissions/db25ccc7-88e1-49f7-8c08-4a9bfff9a4df

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
    prj H V * V = 1 := by
  have h := Matrix.nonsing_inv_mul _ hΓ
  have e : prj H V * V = (Vᴴ * H * V)⁻¹ * (Vᴴ * H * V) := by
    simp only [prj, Matrix.mul_assoc]
  rw [e, h]
end Formalism.FourierDecayAlt.P.HermitianProjections
