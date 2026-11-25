-- Prove2me | solution 1 for Formalism.L2.Th1.A.Two.chordZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:26.492134+00:00
-- url     : https://prove2.me/submissions/e01d8fbd-1d33-4448-b092-c8d5a83fcb45

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_Two_exp_mul_inv
import Theorems.Thm_Formalism_L2_Th1_A_Two_tS_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Plus_equation_C
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_C
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_X
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_apply
import Theorems.Thm_Formalism_L2_Th1_A_chordRegular
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_flowZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.Two
theorem _root_.solution {xP yP : K} (hP : W.toAffine.Equation xP yP) :
    toL ((xPlus W xP yP).subst (expSer W)) = (curveL W).toAffine.addX (xZ W) (HahnSeries.C xP)
      ((yZ W - HahnSeries.C yP) * toL ((tS W xP).subst (expSer W))) := by
  obtain ⟨hX, -⟩ := chordRegular _ (curveL W) (xZ W) (yZ W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL ((tS W xP).subst (expSer W))) (flowZ K W).1.1 (Plus.equation_C W hP)
    (tS_mul W xP)
  have h := exp_mul_inv W
  rw [hX, xZ, yZ]
  simp only [← Wp.sig_apply (he W)]
  simp only [xPlus, nS, tS, map_add, map_sub, map_mul, map_pow, map_ofNat, Wp.sig_C, Wp.sig_X,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  generalize Wp.sig (he W) (invOfUnit (tDen W xP) 1) = v
  generalize Wp.sig (he W) (xS W) = xs
  generalize Wp.sig (he W) (yS W) = ys
  generalize (toL (expSer W))⁻¹ = q at h ⊢
  generalize toL (expSer W) = E at h ⊢
  linear_combination (-(HahnSeries.C W.a₄ - HahnSeries.C W.a₁ * HahnSeries.C yP
        + 2 * HahnSeries.C W.a₂ * HahnSeries.C xP + 3 * HahnSeries.C xP ^ 2) * xs * v ^ 2
          * E ^ 2 * (E * q + 1)
      + (2 * HahnSeries.C yP + HahnSeries.C W.a₁ * HahnSeries.C xP + HahnSeries.C W.a₃) * ys
          * v ^ 2 * E * ((E * q) ^ 2 + E * q + 1)) * h
end Formalism.L2.Th1.A.Two
