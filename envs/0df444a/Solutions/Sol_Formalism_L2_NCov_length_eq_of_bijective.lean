-- Prove2me | solution 1 for Formalism.L2.NCov.length_eq_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:18.602811+00:00
-- url     : https://prove2.me/submissions/220d5bcb-4947-4f61-a7c6-ae922d55b5c8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Module
variable {R R' M M' : Type*} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']
namespace Formalism.L2.NCov
theorem _root_.solution (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Bijective f) :
    Module.length R' M' = Module.length R M := by
  letI := RingHomInvPair.of_ringEquiv φ
  letI := RingHomInvPair.symm (φ : R →+* R') (φ.symm : R' →+* R)
  let e : M ≃ₛₗ[(φ : R →+* R')] M' := LinearEquiv.ofBijective f hf
  rw [Module.length_eq_height, Module.length_eq_height,
    ← Order.height_orderIso (Submodule.orderIsoMapComap e) ⊤, OrderIso.map_top]
end Formalism.L2.NCov
