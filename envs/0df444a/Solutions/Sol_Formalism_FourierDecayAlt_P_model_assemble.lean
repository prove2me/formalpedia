-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.model_assemble
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:54.571368+00:00
-- url     : https://prove2.me/submissions/6ce58139-891f-415f-b4c4-679555b8bc52

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
theorem _root_.solution : Formalism.FourierDecayAlt.M.ModelAssemble := by
  intro hIS hQP hQS hCP hCPC hFA hFW hCD hLE hLS hSO hTy hR hCA P hP l hl1 hlk
  obtain ⟨L, hL⟩ := hLE P
  have hst := hLS P L hL
  have hstart := hSO P hP l L hL
  refine ⟨L, hL, hst, hstart, ?_⟩
  intro S _ _ w hw
  have hAdm := hCA hIS hQP hQS hTy hR P hP l hl1 hlk S w hw
  obtain ⟨_, _, h3, h4, h5⟩ := hFW (A P) S P.r L (startM P l) w hst hstart hAdm
  refine ⟨hFA (A P) S P.r L (startM P l) w hst hstart hAdm, h3, h4, h5, ?_, ?_⟩
  · exact (hCD (A P) S P.r L (startM P l) (Ty P) (kap P) (fun π Y => x0 P l π Y)
      (fun Y => rfl) (fun Y => rfl) w).2.2
  · intro e π
    exact hCPC hIS hQP hQS hCP S P.k P.u P.u' (rho P π) l P.T P.T' w hl1 hlk (hTy P hP π)
      hP.T_pos hP.T'_pos hw.2.1 hw.2.2 e
end Formalism.FourierDecayAlt.P
