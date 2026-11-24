-- Prove2me | solution 1 for Formalism.IndefR.NX.Core.eEnd_actG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:19.200468+00:00
-- url     : https://prove2.me/submissions/1e319663-b2c6-457e-8cb1-3a77e6114226

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DoubleCosetOperators_GoodPartLeTypeSubspace
import Theorems.Thm_Formalism_IndefR_NX_Core_actG_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField TensorProduct
open Formalism Formalism.IndefR Formalism.IndefR.NX Formalism.IndefR.NX.Core
attribute [instance] RatCore.fieldBase RatCore.numberFieldBase RatCore.fKs RatCore.nfKs RatCore.algKs RatCore.crO RatCore.domO
  RatCore.grpG RatCore.finG RatCore.acgWL RatCore.modWL RatCore.modKsWL RatCore.towWL RatCore.modOLWL
  RatCore.towOLWL RatCore.modOKsWL RatCore.towOKsWL RatCore.nW RatCore.ipW
variable (C : RatCore)
namespace Formalism.IndefR.NX.Core
theorem _root_.solution (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) (eC : C.G → C.L0)
    (hcl : ∀ u g, eC (u * g * u⁻¹) = eC g) (u : C.G) (x : Fm C i j b) :
    eEnd C i j b hst eC (actG C i j b hst u x) = actG C i j b hst u (eEnd C i j b hst eC x) := by
  unfold eEnd
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul]
  rw [← (MulAut.conj u).toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hcl]
  rw [← actG_mul_apply, ← actG_mul_apply]
  congr 2
  group
end Formalism.IndefR.NX.Core
