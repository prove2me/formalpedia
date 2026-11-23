-- Prove2me | solution 1 for Formalism.L2.Th1.H.heisenbergAnalytic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:59.794021+00:00
-- url     : https://prove2.me/submissions/78e4ccdc-fd65-4907-ac4d-a3e4a7b21c70

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : OpUAnalytic := by
  intro V _ _ _ H x F hF z _
  let L : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => H v x
      map_add' := fun a b => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c a => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hlin : AnalyticAt ℂ (fun v => H v x) z := (LinearMap.toContinuousLinearMap L).analyticAt z
  have hF' : AnalyticAt ℂ (fun v => F (v + x)) z :=
    AnalyticAt.comp (x := z) (f := fun v => v + x) (hF (z + x) (Set.mem_univ _))
      (analyticAt_id.add analyticAt_const)
  have hE : AnalyticAt ℂ
      (fun v => Complex.exp (-(Real.pi : ℂ) * H v x - (Real.pi : ℂ) * H x x / 2)) z :=
    ((analyticAt_const.mul hlin).sub analyticAt_const).cexp
  exact hF'.mul hE
end Formalism.L2.Th1.H
