-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LemB.len_equiv_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:33.51275+00:00
-- url     : https://prove2.me/submissions/77d56a12-d9ba-416b-85b0-4c60a61a64b6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_CoordinateLengths_PairingContinuityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LemB
namespace Formalism.L2.GlobalTheoryTheory.LemB
theorem _root_.solution {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] M') : Module.length R M = Module.length R' M' := by
  let e' : Submodule R M ≃o Submodule R' M' := Submodule.orderIsoMapComap e
  unfold Module.length
  congr 1
  exact Order.krullDim_eq_of_orderIso e'
end Formalism.L2.GlobalTheoryTheory.LemB
