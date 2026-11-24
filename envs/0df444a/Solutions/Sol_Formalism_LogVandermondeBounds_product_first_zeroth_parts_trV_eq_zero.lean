-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.trV_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:38:59.14709+00:00
-- url     : https://prove2.me/submissions/9079d305-dad6-4848-b8fb-05f4521ab0b7

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_nmV_eq_image
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
theorem _root_.solution (ψ : (Fin r → k) → R) (h : ∀ y, y ≠ 0 → nmV ψ y = 0) : trV ψ = 0 := by
  classical
  let π : (Fin r → k) → Quotient (MulAction.orbitRel kˣ (Fin r → k)) := Quotient.mk _
  unfold trV
  rw [← Finset.sum_fiberwise_of_maps_to (g := π)
    (t := (univ.filter (fun x : Fin r → k => x ≠ 0)).image π)
    (fun x hx => Finset.mem_image_of_mem π hx)]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx0
  have hfib : (univ.filter (fun x : Fin r → k => x ≠ 0)).filter (fun x => π x = π x0) =
      univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x0) := by
    ext y
    rw [mem_image_orbit]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, π, Quotient.eq,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨_, hu⟩
      exact hu
    · rintro ⟨u, rfl⟩
      refine ⟨?_, ⟨u, rfl⟩⟩
      intro h0
      apply hx0
      have h1 := congrArg (fun z => u⁻¹ • z) h0
      simp only [smul_zero, smul_smul, inv_mul_cancel, one_smul] at h1
      exact h1
  rw [hfib, ← nmV_eq_image ψ hx0]
  exact h x0 hx0
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
