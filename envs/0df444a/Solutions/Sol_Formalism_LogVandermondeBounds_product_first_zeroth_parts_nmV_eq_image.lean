-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmV_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:51.076353+00:00
-- url     : https://prove2.me/submissions/3c44e82f-4c0d-4c1a-a4f5-57cebb4e206b

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_exists_coord_ne_zero

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
theorem _root_.solution (ψ : (Fin r → k) → R) {x : Fin r → k} (hx : x ≠ 0) :
    nmV ψ x = ∑ y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x), ψ y := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hx
  unfold nmV diaV
  rw [Finset.sum_image]
  intro c _ d _ h
  have h' := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at h'
  have h'' : ((c⁻¹ : kˣ) : k) = ((d⁻¹ : kˣ) : k) := mul_right_cancel₀ hi h'
  exact inv_inj.1 (Units.ext h'')
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
