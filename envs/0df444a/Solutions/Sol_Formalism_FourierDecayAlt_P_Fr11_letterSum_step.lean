-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.letterSum_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:25.086136+00:00
-- url     : https://prove2.me/submissions/ddc7efb7-3468-4e36-b4c7-48f5c747475d

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_single_eU

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
theorem _root_.solution (l : Letter ℂ S) (Y : ℂ) (hY : Y ≠ l.pt) :
    ∀ (w v : List (Letter ℂ S)), (∀ l' ∈ w, l.intersection_update_fsHerm_neg_one ≠ l'.intersection_update_fsHerm_neg_one ∧ Y ≠ l'.pt ∧ l.pt ≠ l'.pt) →
      Ph (eU l.intersection_update_fsHerm_neg_one 0 0 : SlopeTestRemainingChoices S A) (eU l.intersection_update_fsHerm_neg_one 1 1) (Y - l.pt)⁻¹ (letterSum v w Y) (letterSum v w l.pt) =
        letterSum (l :: v) w Y
  | [], v, _ => by simp [letterSum, Ph_zero]
  | l' :: w, v, h => by
    obtain ⟨h1, h2, h3⟩ := h l' (by simp)
    have ih := solution l Y hY w (v ++ [l']) (fun l'' hl => h l'' (by simp [hl]))
    simp only [letterSum]
    rw [Ph_add, ih, Ph_res _ _ _ _ _ _ h2 h3 hY, ← mult_single, ← mul_assoc, mult_single_eU _ _ _ h1,
      mul_assoc, ← mult_cons, List.cons_append]
end Formalism.FourierDecayAlt.P.Fr11
