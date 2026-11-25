-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.capAdInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:32:08.911859+00:00
-- url     : https://prove2.me/submissions/ae9696b8-ef00-4c70-acbe-88afb75d00e8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapAdInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EH_HGl
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EH_HA
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EH_HC
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EH_HL
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EH_HS
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EHc_HL
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EHc_change
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ad_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution : CapAdInv := by
  intro k r E _ _ y u f hy hf h hh
  have hyu := gv_unit hy
  have hQP : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hyu
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  set e : Fin (Q.mdim k r 0) ≃ Fin (2 * r + k + 1) := finCongr hm with he
  have hpos : Q.posL k r 0 = ⇑e := by
    funext j; apply Fin.ext; simp [Q.posL, he]
  rw [hpos]
  exact ad_main (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl (EHc k r y) (EHc_HL hy) hQP
    (fun c d φ hφ g hg => EHc_change hy c d φ hφ g hg) e u f (by rw [hm]; exact hf) h hh
end Formalism.FourierDecayAlt.P.JFxE
