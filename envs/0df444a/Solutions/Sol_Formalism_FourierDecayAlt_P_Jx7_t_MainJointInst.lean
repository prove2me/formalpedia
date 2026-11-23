-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_MainJointInst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:33.584142+00:00
-- url     : https://prove2.me/submissions/f9d70e51-4a0f-4aad-828c-34e063212a7f

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_FrameProducts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_InstSizes
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_LatticeSumsJoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_GlobPositive
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_SizesToRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_InstLatticeSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_XIsLamOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_MainJointForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : MainJointInst := by
  intro hA hS hBox hLat hId hNorm hDeg C₄ Cthr h4
  obtain ⟨C₁, hC1, hIL⟩ := t_InstLatticeSums t_LatticeSumsJoint t_InstSizes hBox hLat
    hId hNorm hDeg t_FrameProducts t_XIsLamOne
  obtain ⟨CA, C, b1, b2, b3, b4, hM⟩ := t_MainJointForm hA hS C₁ C₄ Cthr hC1 h4
  refine ⟨CA, C, b1, b2, b3, b4, ?_⟩
  intro C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k1, hk1⟩ := hM C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k2, hk2⟩ := t_SizesToRecursion hS CA C0 CG CDel cT Cb C 0 b2 hC0 hCG hCDel hcT hCb hcTb
    b3 b4
  obtain ⟨k3, hk3⟩ := t_GlobPositive CDel Cb hCDel hCb
  refine ⟨max (max k1 k2) k3, ?_⟩
  intro E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf hU hInst jn H
    _ _ _ Vt c hrec he P _ B he1 hI hδ hrow
  obtain ⟨hg1, hg2, hlen⟩ := hk3 (InfinitePlace E) G bb (le_trans (le_max_right _ _) hk) hyp.1
  have s := hk2 (InfinitePlace E) G bb Cp Cf Th de de' T T' du du' l
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk) hyp h16 hCf
  have hTh4 : 4 < Th := s.2.1
  have hGr : IsGreatest (G.thrSet CA de de' T T' l) ((Th ^ G.f)⁻¹) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hyp
    exact h
  obtain ⟨hSB, hLS⟩ := hIL E W D e G CA de de' T T' l Th hU hInst hg1 hg2 (by linarith) hlen hTh4 hGr
  have hf : D.f = G.f := by
    have := Fintype.card_congr e
    rw [Fintype.card_fin] at this
    exact this
  have hf1 : 1 ≤ D.f := by
    obtain ⟨_, d2, d3⟩ := hDeg E
    rw [hf]; unfold Sz.Glob.f; omega
  have hK : 4 ≤ D.K := by rw [hInst.2.1]; norm_num
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := hrec
  exact hk1 (InfinitePlace E) G bb Cp Cf Th de de' T T' du du' l
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk) hyp h16
    hCf E W D jn H Vt c hInst.1 hf
    ⟨hK, hf1, by linarith, hSB, r1, r2, r3, r4, r5, r6, r7, r8, r9, hLS, r10, r11, r12⟩ he P B he1 hI hδ
    hrow
end Formalism.FourierDecayAlt.P.Jx7
