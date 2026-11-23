-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.mult_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:24.577933+00:00
-- url     : https://prove2.me/submissions/4a3fb26b-7d42-46a1-b431-a77326c2c774

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_one
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
theorem _root_.solution (γ : ℂ) : (mult ([] : List (Letter ℂ S)) γ : SlopeTestRemainingChoices S A) = 1 := by
  simp only [mult_eq, List.map_nil, List.prod_nil]
  exact dg_one
end Formalism.FourierDecayAlt.P.Fr11
