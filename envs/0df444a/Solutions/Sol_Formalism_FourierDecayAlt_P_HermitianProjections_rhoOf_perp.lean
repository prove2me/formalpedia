-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.rhoOf_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:45:22.684855+00:00
-- url     : https://prove2.me/submissions/efc40e47-4f03-4fc5-980d-acd8464d2dee

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_prj_perp

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
theorem _root_.solution (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (x : n → ℂ)
    (hx : (Vᴴ * H) *ᵥ x = 0) : rhoOf H V Φ *ᵥ x = x := by
  simp only [rhoOf]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, prj_perp H V x hx, Matrix.mulVec_zero,
    add_zero]
end Formalism.FourierDecayAlt.P.HermitianProjections
