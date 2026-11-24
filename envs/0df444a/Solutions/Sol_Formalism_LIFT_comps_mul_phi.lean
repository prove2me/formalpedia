-- Prove2me | solution 1 for Formalism.LIFT.comps_mul_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:32:02.618836+00:00
-- url     : https://prove2.me/submissions/cb1a89eb-a5cf-4253-beed-ee15c03994b0

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Finset
variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)
namespace Formalism.LIFT
theorem _root_.solution (s : A) {x : A} (hx : Comps φA ε aa ℓ x) :
    Comps φA ε aa ℓ (φA s * x) := by
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨fun i => s * e i, fun i => aa.mul_mem_left s (he i), ?_⟩
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_mul]; ring
end Formalism.LIFT
