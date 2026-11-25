-- Prove2me | solution 1 for Formalism.IndefR.NX.Core.goodPart_le_typeSubspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:11.064539+00:00
-- url     : https://prove2.me/submissions/9e34f1ce-c713-49e1-ad90-ae30bfd064af

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DoubleCosetOperators_GoodPartLeTypeSubspace
import Theorems.Thm_Formalism_IndefR_NX_Core_eEnd_actG

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
theorem _root_.solution (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) (U : Subgroup C.G)
    (psiU : U →* (FractionRing (C.O i))ˣ) (eC : C.G → C.L0) (hcl : ∀ u g, eC (u * g * u⁻¹) = eC g) :
    V0 C i j b hst U psiU eC ≤ Fm0 C i j b hst U psiU := by
  rintro y ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Fm0, Submodule.mem_iInf] at hx
  rw [Fm0, Submodule.mem_iInf]
  intro u
  have h := hx u
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply] at h
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
  change actG C i j b hst u (eEnd C i j b hst eC x) = _
  rw [← eEnd_actG C i j b hst eC hcl]
  change eEnd C i j b hst eC ((actG C i j b hst u : Fm C i j b →ₗ[FractionRing (C.O i)] Fm C i j b) x) = _
  rw [h, map_smul]
end Formalism.IndefR.NX.Core
