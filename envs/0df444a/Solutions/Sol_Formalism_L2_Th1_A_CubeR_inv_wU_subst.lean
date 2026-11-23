-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.inv_wU_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:14.49088+00:00
-- url     : https://prove2.me/submissions/be425cd3-38d3-4820-81d2-04f3f36cc156

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wU_mul_xS
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CubeR
open Univ CurveSer
local notation "cc" => MvPowerSeries.constantCoeff
variable {σ : Type*} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
namespace Formalism.L2.Th1.A.CubeR
theorem _root_.solution {K : Type u} [Field K] (W : WeierstrassCurve K) {a : MvPowerSeries σ K}
    (ha : cc a = 0) : ((Formalism.ELL.wU (wSer W)).subst a)⁻¹ = (xS W).subst a := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero ha
  have h1 : (xS W).subst a * (wU W).subst a = 1 := by
    rw [← subst_mul hs, mul_comm, wU_mul_xS, ← coe_substAlgHom hs, map_one]
  have h0 : cc ((wU W).subst a) ≠ 0 := by
    intro h
    have := congrArg cc h1
    rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  exact (MvPowerSeries.inv_eq_iff_mul_eq_one h0).2 h1
end Formalism.L2.Th1.A.CubeR
