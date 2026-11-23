-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.mem_image_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:29.227139+00:00
-- url     : https://prove2.me/submissions/7693fda8-b02a-4f7a-9f9c-b2c487c05201

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution {x : Fin r → k} (y : Fin r → k) :
    y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x) ↔ ∃ u : kˣ, u • x = y := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c⁻¹, by rw [Units.smul_def]⟩
  · rintro ⟨u, rfl⟩; exact ⟨u⁻¹, by rw [inv_inv, Units.smul_def]⟩
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
