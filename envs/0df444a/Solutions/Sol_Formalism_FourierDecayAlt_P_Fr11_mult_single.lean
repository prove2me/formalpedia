-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.mult_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:42.527808+00:00
-- url     : https://prove2.me/submissions/72efcced-54d7-48e0-a02e-007189376239

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_eU_same
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
theorem _root_.solution (l : Letter ℂ S) (γ : ℂ) :
    (mult [l] γ : SlopeTestRemainingChoices S A) =
      (1 + 1 / (l.pt - γ)) • eU l.intersection_update_fsHerm_neg_one 0 0 + (1 - 1 / (l.pt - γ)) • eU l.intersection_update_fsHerm_neg_one 1 1 := by
  rw [mult_eq, eU_same, eU_same, dg_smul, dg_smul, dg_add]
  congr 1
  funext e
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  generalize e l.intersection_update_fsHerm_neg_one = k
  fin_cases k <;> simp [sg] <;> ring
end Formalism.FourierDecayAlt.P.Fr11
