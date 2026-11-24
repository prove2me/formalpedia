-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.rhoOf_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:19:42.719258+00:00
-- url     : https://prove2.me/submissions/0bb5c3b5-295f-465e-833c-8533bd496a5f

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_prj_mul

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
theorem _root_.solution (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) :
    rhoOf H V Φ * V = V * Φ := by
  simp only [rhoOf]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (V * (Φ - 1)), prj_mul H V hΓ, Matrix.mul_one,
    Matrix.mul_sub, Matrix.mul_one]
  abel
end Formalism.FourierDecayAlt.P.HermitianProjections
