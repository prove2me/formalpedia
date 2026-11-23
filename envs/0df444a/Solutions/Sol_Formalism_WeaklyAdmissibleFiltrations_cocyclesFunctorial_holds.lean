-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.cocyclesFunctorial_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:20.300036+00:00
-- url     : https://prove2.me/submissions/e4bb7664-dbfe-447b-8ffb-77285322f47c

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : CocyclesFunctorial := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V V' _ _ _ _ _ _ _ _ ρ ρ'
    _ _ _ _ _ _ _ f hf hequiv c
  have hZ : c ∈ continuousCocycles ρ → ⇑f ∘ c ∈ continuousCocycles ρ' := by
    rintro ⟨hc1, hc2⟩
    refine ⟨hf.comp hc1, fun g h => ?_⟩
    change f (c (g * h)) = f (c g) + ρ' g (f (c h))
    rw [hc2, map_add, hequiv]
  refine ⟨hZ, ?_⟩
  rintro ⟨hc, x, hx⟩
  let m := AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)
  have hm : ∀ g y, m (actVB PD ρ g y) = actVB PD ρ' g (m y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, actVB, hequiv]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨hZ hc, m x, fun g => ?_⟩
  change f (c g) ⊗ₜ[Qp] (1 : B) = _
  have := congrArg m (hx g)
  simp only [m, AlgebraTensorModule.map_tmul, LinearMap.id_apply, map_sub] at this
  rw [this, ← hm]
end Formalism.WeaklyAdmissibleFiltrations
