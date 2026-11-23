-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.mult_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:42.411859+00:00
-- url     : https://prove2.me/submissions/b6de4b02-776b-4154-be6b-886f36f3da30

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (l : Letter ℂ S) (v : List (Letter ℂ S)) (γ : ℂ) :
    (mult (l :: v) γ : SlopeTestRemainingChoices S A) = mult [l] γ * mult v γ := by
  simp only [mult_eq, dg_mul, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
end Formalism.FourierDecayAlt.P.Fr11
