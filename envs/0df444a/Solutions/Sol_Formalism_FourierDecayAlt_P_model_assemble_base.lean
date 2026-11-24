-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.model_assemble_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:54.802425+00:00
-- url     : https://prove2.me/submissions/671572a7-4e67-4c12-894f-324e2ecaa15d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Mx9
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.ModelAssembleBase := by
  intro hIS hIS2 hQP hQS hCPB hCPCB hFAR hARB hWJ hCD hLE hLS hSO hTy hR hCAB P hP l hl1 hlk
  obtain ⟨L, hL⟩ := hLE P
  have hst := hLS P L hL
  have hstart := hSO P hP l L hL
  refine ⟨L, hL, hst, hstart, ?_⟩
  intro S _ _ w hw
  have hAB := hCAB hIS hIS2 hQP hQS hTy hR P hP l hl1 hlk S w hw
  have hAR := hARB (A P) S P.r L (startM P l) w hAB
  have hF := hFAR (A P) S P.r L (startM P l) w hst hstart hAR
  obtain ⟨jRR, jTT, _, jN, jreg⟩ := hWJ (A P) S P.r L (startM P l) w
  refine ⟨hF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← jRR, hF.form, FrameData.d, jN]
  · intro Y hY
    have h := hF.frame_τ Y (by rw [jreg]; exact hY)
    rwa [jTT] at h
  · intro Y hY hY1
    have h := hF.frame_l Y hY hY1
    rwa [jTT, FrameData.l] at h
  · exact (hCD (A P) S P.r L (startM P l) (Ty P) (kap P) (fun π Y => x0 P l π Y)
      (fun Y => rfl) (fun Y => rfl) w).2.2
  · intro e π
    exact hCPCB hIS hQP hQS hCPB S P.k P.u P.u' (rho P π) l P.T P.T' w hl1 hlk (hTy P hP π)
      hP.T_pos hP.T'_pos hw.2.1 hw.2.2 e
end Formalism.FourierDecayAlt.P
