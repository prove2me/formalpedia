-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.mem_image_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:46.875508+00:00
-- url     : https://prove2.me/submissions/19f65055-7bfc-491f-ad0a-37c0e4765cfd

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mem_image_orbit

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
theorem _root_.solution {x : Fin r → k} (hx : x ≠ 0) (y : Fin r → k) :
    y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x) ↔ y ≠ 0 ∧ ∃ c : k, y = c • x := by
  rw [mem_image_orbit]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨?_, ⟨(u : k), Units.smul_def u x⟩⟩
    intro h0
    apply hx
    have h1 := congrArg (fun z => ((u⁻¹ : kˣ) : k) • z) h0
    simp only [smul_zero] at h1
    rw [Units.smul_def, smul_smul, u.inv_mul, one_smul] at h1
    exact h1
  · rintro ⟨hy, c, rfl⟩
    have hc : c ≠ 0 := by rintro rfl; exact hy (zero_smul _ _)
    exact ⟨Units.mk0 c hc, by rw [Units.smul_def, Units.val_mk0]⟩
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
