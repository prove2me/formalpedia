-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.capelli_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:11.299573+00:00
-- url     : https://prove2.me/submissions/60914cad-dd25-403c-a4b3-0e77cb162d23

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_commute_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_Qr_mem_CapSp
import Theorems.Thm_Formalism_REAL_qDetCentral_of
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.CapStab := by
  intro V _ _ n E m hE
  refine ⟨fun a b v hv => ?_, fun X hX v hv => ?_⟩
  · rw [mem_CapSp] at hv ⊢
    intro w
    have h := qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds (Module.End ℂ V) n E hE w a b
    have h2 := LinearMap.congr_fun h v
    simp only [Module.End.mul_apply] at h2
    rw [h2, hv w, map_smul]
  · rw [mem_CapSp] at hv ⊢
    intro w
    have h : Commute X (qdet E w) := QuantumMinorCommutation.commute_qminor E id id w X (fun s s' => hX _ _)
    have h2 := LinearMap.congr_fun h.eq v
    simp only [Module.End.mul_apply] at h2
    rw [← h2, hv w, map_smul]
end Formalism.FourierDecayAlt.P
