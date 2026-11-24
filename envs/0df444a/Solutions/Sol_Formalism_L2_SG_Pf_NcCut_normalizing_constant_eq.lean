-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcCut.normalizing_constant_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:05.852121+00:00
-- url     : https://prove2.me/submissions/e9230959-a80e-4509-abdc-6868b7a582c1

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NormalizingConstantEq
import Theorems.Thm_Formalism_L2_SG_Pf_NcCut_MM_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcCut
open Formalism.FourierDecayAlt.S3
variable {P : Type} [Fintype P] (B : MassData P)
namespace Formalism.L2.SG.Pf.NcCut
theorem _root_.solution (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) :
    B.n0c = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat / B.μH' := by
  have hMM := MM_eq B hP hO hT
  obtain ⟨hp, hKo, -, -, -, -, hH, hH', -, -, hN, hN', hZZ, -, -, -, hHa, -, -, -, hB, hVH, -, -, -,
    hCoo, -, -, -, hr0, -⟩ := hP
  obtain ⟨hρ, hNa, -, hNa'⟩ := hMs
  obtain ⟨hS, -, hS', -⟩ := hL
  have hK : 0 < B.μK := by
    unfold MassData.μK
    exact mul_pos hKo (Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1)
  have hvN : B.volN = 1 / B.μN := by
    rw [eq_div_iff hN.ne', ← hNa, hV.1]
  have hvN' : B.volN' = 1 / B.μN' := by
    rw [eq_div_iff hN'.ne', ← hNa', hV.2]
  have hM' : B.n0c * B.ρ0 = B.AA := hM
  unfold MassData.AA at hM'
  rw [hMM, hS, hS'] at hM'
  have hn := eq_div_of_mul_eq hr0.ne' hM'
  rw [hn, hρ, hvN, hvN']
  have h1 := hK.ne'
  have h2 := hH.ne'
  have h3 := hH'.ne'
  have h4 := hN.ne'
  have h5 := hN'.ne'
  have h6 := hZZ.ne'
  have h7 := hHa.ne'
  have h8 := hVH.ne'
  field_simp
end Formalism.L2.SG.Pf.NcCut
