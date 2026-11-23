-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F.t_PairBoundFromLocalNG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:16.970372+00:00
-- url     : https://prove2.me/submissions/bc862322-0b84-4f8f-b91d-abeb9662349c

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_D3_hk
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_F_pos_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
theorem _root_.solution : PairBoundFromLocalNG := by
  intro hPBL hPBC hRow hCh hLoop C₄ Cthr CL hC4 hCL C1 C0n A CB CSt Cg CT hCB hCSt hCg hCT hA
  obtain ⟨hMR, hPB, hLC, hGC, hLL, hAx, hA13, hPBA, hPI, hEI, hPS, hSF, hNP, hNE, hND, hNL, hNNG, hNGE,
    hEZ⟩ := hPBC
  obtain ⟨hNDS, hDS, hS0, hGS, hB3, hLJ, hLGR⟩ := hLoop
  obtain ⟨CA, C, h1, h2, h3, h4, hrest⟩ := hPBL hMR hPB hLC hGC hLL hAx hA13 hPBA hPI hEI hPS hSF hNP hNE
    hND hNL hNNG hNGE hEZ C₄ Cthr hC4
  obtain ⟨K₀, hK⟩ := hLJ hNDS hDS hS0 hGS hB3 CL hCL
  obtain ⟨Cn, hCn0, hCn⟩ := hRow hCh C1 C0n A CB CSt Cg CT hCB hCSt hCg hCT hA
  refine ⟨CA, C, K₀, Cn, h1, h2, h3, h4, hCn0, ?_⟩
  intro C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  obtain ⟨k0, hk0⟩ := hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  refine ⟨k0, ?_⟩
  intro E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk hSz hc1 hc2 hUn hInst hLM jn H _ _ _ Vt c sd
    hRI hDI P _ B hRows hMassData hEL τ Rw I HS H₁ _ _ _ _ _ _ X hLink hSplit hSN Al NT Gam Xi hAl hPar hXi
    hlog hLI Cl Nu N cSt e1 Irat Ire hFI hNS hNI
  have hAbs : X.AbsConv := hSplit.1
  have hLink' := hLink
  obtain ⟨hG1, hSig, htyp, hd, hd', hDs⟩ := hLink'
  obtain ⟨bPos, bForm, bMass, bJac, bNu, bInf, bVol, bLev, bMas, bCol, bOrd, bTyp, bInd⟩ := hMassData
  have hNormI : NormInputs B := ⟨bPos, bJac, bNu, bInf, bVol, bLev, bMas, bCol, bOrd, bTyp, bInd⟩
  have hddpos := (pos_facts B bPos).2
  rw [hd, hd', hDs] at hddpos
  have hloops := hK τ Rw I HS H₁ X G.k G.r G.f Al bb G.g G.v NT Gam Xi _ hAl hPar hXi hlog hddpos.le hLI
  obtain ⟨hBig, hNSc⟩ := hLGR hSF τ Rw I HS H₁ X _ _ hAbs hloops
  have hng := hCn E τ Rw I HS H₁ X G.r G.k Cl Nu N P B bb (2 * G.v) G.g ((T : ℝ) * T') cSt e1 Irat Ire hAbs
    hG1 hNormI hFI hNS hNI
  rw [hd, hd', hDs] at hng
  exact hk0 E W D e G bb Cp Cf Th de de' T T' du du' l hk hSz hc1 hc2 hUn hInst hLM jn H Vt c sd hRI hDI P B
    hRows ⟨bPos, bForm, bMass, bJac, bNu, bInf, bVol, bLev, bMas, bCol, bOrd, bTyp, bInd⟩ hEL τ Rw I HS H₁ X
    (1 / 3) Cn hLink hSplit hSN hBig hNSc hng
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
