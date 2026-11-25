-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.induction_from_assembled_pieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:04:03.258726+00:00
-- url     : https://prove2.me/submissions/93395afe-2f0d-47fb-a78a-30893eadaa51

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open AveragedKernelSums
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.ThetaExistenceInductiveFromPieces := by
  intro aAvg aGH aSt aGP aG aGK aGI aTO aStep
  intro hMS hPO hON hPG hGR hEB hPC hBS hLF hILR hIKR hVS hPL hCM hPD hLC hMLC hSU hSM' hRF hRS hEx
  intro hHD hGM hGIn hGAS
  intro hNS hML hOR hOI hHR hKB hKH hShU hShS hCS hRC hSN hPhD hLoc hCV hXV hCA hUG hUN hCP hUB hAD
    hCN hTL
  intro hTB hTS hSM hC1 hMM hIF hKG hKBD hNSup
  have hAB : AvgBound := aAvg hMS hPO hON
  have hGH : GaussHess := aGH hGM hGIn hHD hMM hVS
  have hSP : StationaryPhase :=
    aSt hNS hML hIKR hMM hRF hLC hPL hMLC hOI hVS hRS hSM' hGAS hLF
  have hGP : GermPhi := aGP hOR hSP hOI hMM
  have hG : Germ := aG hHR hGP
  have hGK : GermKernel := aGK hG hKB hIF hRF
  intro hA2 hN1
  have hGI : GermIdentity :=
    aGI hGH hGK hKH hA2.2 hMM hRF hShU hShS hCS hRC hSN hPhD hLoc hMLC hILR hCV hXV
  have hTO : ThOm := aTO hGI hAD hLoc hKH hMLC hLC hLF hShU hSU hUG hUN hCP hUB hCA hMM hKG hKBD
    hGR hAB hPG hPD hPL hCM hCN hTL hTB hTS
  exact aStep hTO hSM hNSup hC1 hEx hLF hEB hPC hBS hA2 hN1
end Formalism.FourierDecayAlt.P
