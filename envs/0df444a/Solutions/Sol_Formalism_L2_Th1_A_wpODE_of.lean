-- Prove2me | solution 1 for Formalism.L2.Th1.A.wpODE_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:03:59.872617+00:00
-- url     : https://prove2.me/submissions/ab685731-99b5-4109-96a7-326dcf6fda83

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ConstCurveDL
import Theorems.Thm_P2M_Formalism_L2_Th1_A_Wp_isDer_dL__14cb087f2915
import Theorems.Thm_Formalism_L2_Th1_A_Wp_constCurve_dL
import Theorems.Thm_Formalism_L2_Th1_A_flowZ_of
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_flowWeierstrassForm
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
open Wp
namespace Formalism.L2.Th1.A
theorem _root_.solution (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : WpODE.{u} := by
  intro K _ _ W
  have hF := (flowZ_of hE hC K W).1
  have h6 : IsUnit (6 : LaurentSeries K) := by
    have h := (IsUnit.mk0 (6 : K) (by norm_num)).map (HahnSeries.C : K →+* LaurentSeries K)
    rwa [map_ofNat] at h
  have hb : 12 * (HahnSeries.C (W.b₂ / 12) : LaurentSeries K) = (curveL W).b₂ := by
    rw [WeierstrassCurve.map_b₂, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    field_simp
  have hg2 : 12 * (HahnSeries.C (g₂ W) : LaurentSeries K) = (curveL W).c₄ := by
    rw [WeierstrassCurve.map_c₄, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    rw [g₂]
    field_simp
  have hg3 : 216 * (HahnSeries.C (g₃ W) : LaurentSeries K) = (curveL W).c₆ := by
    rw [WeierstrassCurve.map_c₆, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 216, ← map_mul]
    congr 1
    rw [g₃]
    field_simp
  obtain ⟨h1, h2, h3⟩ := flowWeierstrassForm _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C (W.b₂ / 12))
    (HahnSeries.C (g₂ W)) (HahnSeries.C (g₃ W)) isDer_dL' (constCurve_dL W) hF h6 hb hg2 hg3
  refine ⟨?_, h2, ?_⟩
  · simpa only [wpL, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] using h1
  · have hh : (HahnSeries.C (1 / 2 : K) : LaurentSeries K) * 2 = 1 := by
      rw [← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 2, ← map_mul, ← map_one HahnSeries.C]
      congr 1
      norm_num
    have hg : (HahnSeries.C (g₂ W / 2) : LaurentSeries K)
        = HahnSeries.C (1 / 2 : K) * HahnSeries.C (g₂ W) := by
      rw [← map_mul]
      congr 1
      ring
    rw [hg]
    change 2 * dL (dL (wpL W)) = 12 * wpL W ^ 2 - HahnSeries.C (g₂ W) at h3
    linear_combination HahnSeries.C (1 / 2 : K) * h3 - (dL (dL (wpL W)) - 6 * wpL W ^ 2) * hh
end Formalism.L2.Th1.A
