-- Prove2me | solution 1 for Formalism.L2.Th1.A.addition_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:48:20.297275+00:00
-- url     : https://prove2.me/submissions/01068062-242c-4d96-ba1e-59d4c5ed52c0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_Two_tS_mul
import Theorems.Thm_Formalism_L2_Th1_A_Two_chordZ
import Theorems.Thm_Formalism_L2_Th1_A_Two_isFlow_subst
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_Plus_equation_C
import Theorems.Thm_Formalism_L2_Th1_A_Wp_constCurve_dL
import Theorems.Thm_Formalism_L2_Th1_A_flowLogDeriv
import Theorems.Thm_Formalism_L2_Th1_A_flowZ
import Theorems.Thm_Formalism_L2_Th1_A_plusFlow
import Theorems.Thm_P2M_Formalism_L2_Th1_A_Wp_isDer_dL__14cb087f2915


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Two
namespace Formalism.L2.Th1.A
theorem _root_.solution : PlusZ.{u} := by
  intro K _ _ W xP yP hP
  refine ⟨isFlow_subst W (plusFlow K W xP yP hP).1, tS_mul W xP, ?_⟩
  have h := flowLogDeriv _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C xP) (HahnSeries.C yP)
    (toL ((tS W xP).subst (expSer W))) Wp.isDer_dL' (Wp.constCurve_dL W) (flowZ K W).1
    (Plus.equation_C W hP) (dL_C _) (dL_C _) (tS_mul W xP)
  rw [WeierstrassCurve.Affine.map_negY] at h
  have hw : dL (wpL W) = dL (xZ W) := by rw [wpL, map_add, dL_C, add_zero]
  rw [hw, chordZ W hP, chordZ W ((WeierstrassCurve.Affine.equation_neg xP yP).2 hP), h]
end Formalism.L2.Th1.A
