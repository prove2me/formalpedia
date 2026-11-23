-- Prove2me | solution 1 for Formalism.LIFT.comps_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:20.144633+00:00
-- url     : https://prove2.me/submissions/ab302f46-b8bb-4f74-8f58-8668b7f10ccf

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
theorem _root_.solution {x y : A} (hx : Comps φA ε aa ℓ x) (hy : Comps φA ε aa ℓ y) :
    Comps φA ε aa ℓ (x + y) := by
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨e', he', rfl⟩ := hy
  refine ⟨e + e', fun i => aa.add_mem (he i) (he' i), ?_⟩
  simp [map_add, mul_add, sum_add_distrib]
end Formalism.LIFT
