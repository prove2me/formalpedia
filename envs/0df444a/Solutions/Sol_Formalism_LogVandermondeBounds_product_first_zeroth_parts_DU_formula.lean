-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.DU_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:35.735791+00:00
-- url     : https://prove2.me/submissions/8ef85bfb-a6ee-4b6a-b1fc-a20ea840a1b8

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pair_smul_right
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_nmV_eq_image
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mem_image_line
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_count1
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_count2

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
theorem _root_.solution (hr : 2 ≤ r) (ψ : (Fin r → k) → R) (x : Fin r → k) (hx : x ≠ 0) :
    opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x
      - ((Fintype.card k : R)) ^ (r - 2) * nmV ψ x + ((Fintype.card k : R)) ^ (r - 2) * trV ψ := by
  have h1 : opD (opU ψ) x = ∑ y, ((univ.filter (fun f : Fin r → k =>
      pair f x = 1 ∧ pair f y = 1)).card : R) * ψ y := by
    unfold opD opU
    rw [Finset.sum_comm' (t' := univ)
      (s' := fun y => univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f y = 1))]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    · intro f y; simp
  have h2 : ∀ y, ((univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f y = 1)).card : R) * ψ y =
      (if y = x then ((Fintype.card k : R)) ^ (r - 1) * ψ y else 0) +
      (if ∀ c : k, y ≠ c • x then ((Fintype.card k : R)) ^ (r - 2) * ψ y else 0) := by
    intro y
    by_cases hyx : y = x
    · rw [hyx]
      have hne : ¬ ∀ c : k, x ≠ c • x := fun h => h 1 (one_smul _ _).symm
      rw [if_pos rfl, if_neg hne, add_zero]
      have : univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f x = 1) =
          univ.filter (fun f => pair f x = 1) := by
        ext f; simp
      rw [this, count1 hx 1]; push_cast; ring
    · rw [if_neg hyx]
      by_cases hl : ∀ c : k, y ≠ c • x
      · rw [if_pos hl, zero_add, count2 hr hx hl 1 1]; push_cast; ring
      · rw [if_neg hl]
        push_neg at hl
        obtain ⟨c, rfl⟩ := hl
        have hc : c ≠ 1 := by rintro rfl; exact hyx (one_smul _ _)
        rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 (fun f _ h =>
          hc (by rw [← h.2, pair_smul_right, h.1, mul_one])))]
        simp
  have htr : trV ψ = nmV ψ x + ∑ y ∈ univ.filter (fun y => ∀ c : k, y ≠ c • x), ψ y := by
    unfold trV
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun y : Fin r → k => y ≠ 0))
      (fun y => ∃ c : k, y = c • x)]
    congr 1
    · rw [nmV_eq_image ψ hx]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext y
      rw [mem_image_line hx]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, ne_eq]
      exact ⟨fun h => h.2, fun h => ⟨fun h0 => h 0 (by simp [h0]), h⟩⟩
  rw [h1, Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), htr]
  have h3 : ∑ y, (if ∀ c : k, y ≠ c • x then ((Fintype.card k : R)) ^ (r - 2) * ψ y else 0) =
      ((Fintype.card k : R)) ^ (r - 2) * ∑ y ∈ univ.filter (fun y => ∀ c : k, y ≠ c • x), ψ y := by
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [h3]; ring
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
