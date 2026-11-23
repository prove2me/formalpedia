-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.Kw_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:23.93257+00:00
-- url     : https://prove2.me/submissions/16c1acf9-d8f4-4368-a456-1ef556bb31b4

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_eU_same
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_io

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
theorem _root_.solution {r : ℕ} (L : LevelData A r) (l : Letter ℂ S) (w : List (Letter ℂ S)) :
    (Kw L (l :: w) : SlopeTestRemainingChoices S A) = Kw L w + eU l.intersection_update_fsHerm_neg_one 0 0 * tz L := by
  have hc : (eU l.intersection_update_fsHerm_neg_one 0 0 : SlopeTestRemainingChoices S A) * tz L = tz L * eU l.intersection_update_fsHerm_neg_one 0 0 := by
    rw [eU_same, tz]
    exact dg_io _ _
  simp only [Kw]
  rw [hc, ← mul_add]
  congr 1
  rw [eU_same]
  unfold dg
  rw [Matrix.diagonal_add]
  congr 1
  funext e
  by_cases h : e l.intersection_update_fsHerm_neg_one = 0 <;> simp [List.filter_cons, h]
end Formalism.FourierDecayAlt.P.Fr11
