-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.divisibility_of_theorem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:17:04.341825+00:00
-- url     : https://prove2.me/submissions/5a89b9cc-800a-42b4-a2df-1c383aacc761

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_divisibility_of_conclusion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBrDiv
theorem _root_.solution : DivOfThm := by
  intro T U0 W Top _ m f D C P logOm Pl _ e _ aP St haP hFo hC hP hS
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33⟩ := hP
  have hb : 0 < D.b := by rw [p4]; exact Real.exp_pos _
  have hx0 : 0 ≤ D.x := by linarith
  have ha : 0 ≤ D.a := by rw [p5]; exact mul_nonneg hx0 hb.le
  have hLa : 0 ≤ D.La := le_trans (abs_nonneg _) p22
  have hB0 : 0 ≤ D.B0 := by
    rw [p10]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb.le) (Real.rpow_nonneg hx0 _)
  refine divisibility_of_conclusion U0 W Top m f D C logOm P.C0 Pl e aP (fun u0 => D.Fo u0 / 2) haP
    (fun u0 => by ring) hC.ge ha hLa (by linarith) hx0 ?_
  intro u0 u
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17⟩ := hS u0 u
  have hF : D.Fo u0 / 2 = (St u0 u).FoP := by rw [hFo u0 u]; ring
  rw [hF]
  exact T (Fin m) Pl (Finset.univ.map e) (D.muCC u0) (St u0 u).mu0 (St u0 u).FoP (D.h u0 u) (St u0 u).hP
    (St u0 u).mlam (Real.log (D.T u0 u)) (St u0 u).hK aP (St u0 u).phν (St u0 u).nν (St u0 u).fa
    D.x D.ε D.L D.b D.a P.rd D.La D.B0 D.Nc (D.x ^ (C.eDiv * D.ε)) (m : ℝ) P.f D.k P.N P.S P.tt P.η P.w'' D.b'
    P.dC P.lam0 P.C0 (St u0 u).Lpass (St u0 u).Eb (St u0 u).e6 (St u0 u).eP logOm (St u0 u).eK (St u0 u).pq
    (St u0 u).w (St u0 u).eE (St u0 u).δ
    s1 s2 s3 s4 s5 s6 s7 s8 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 (by simp) p13 p14 p15 p16 p17 p18 p19 p20 p21
    s9 s10 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 s11 s12 s13 s14 s15 s16 s17
end Formalism.LFunctionChainParameters.LBrDiv
