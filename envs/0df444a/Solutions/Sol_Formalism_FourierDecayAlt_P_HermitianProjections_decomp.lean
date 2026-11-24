-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:55:20.205638+00:00
-- url     : https://prove2.me/submissions/14aca1c5-885c-454c-9431-a32369a260da

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_K_eq

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
theorem _root_.solution (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) (x : n → ℂ) :
    (Vᴴ * H) *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = 0 := by
  have hK := K_eq H V hΓ
  have e : (Vᴴ * H) *ᵥ (V *ᵥ (prj H V *ᵥ x)) = ((Vᴴ * H * V) * prj H V) *ᵥ x := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [Matrix.mulVec_sub, e, ← hK, sub_self]
end Formalism.FourierDecayAlt.P.HermitianProjections
