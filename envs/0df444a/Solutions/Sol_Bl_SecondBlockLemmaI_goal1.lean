-- Prove2me | solution 1 for Bl.SecondBlockLemmaI.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:49.071039+00:00
-- url     : https://prove2.me/submissions/b9f16487-3425-422b-a615-d84de2161ab5

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasH_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Polynomial
open Bl Bl.SecondBlockLemmaI
variable {A : Type} [CommRing A] (I : Ideal A)
namespace Bl.SecondBlockLemmaI
theorem _root_.solution [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by
  have hm : (X ^ 2 - X : A[X]).Monic := by
    exact monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num))
  have h0 : (X ^ 2 - X : A[X]).eval ε ∈ I := by
    simp only [eval_sub, eval_pow, eval_X]
    rw [pow_two]; exact h
  have hu : IsUnit (Ideal.Quotient.mk I ((X ^ 2 - X : A[X]).derivative.eval ε)) := by
    have hd : (X ^ 2 - X : A[X]).derivative.eval ε = 2 * ε - 1 := by
      simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_pow,
        eval_X, eval_one, eval_C]
      norm_num
    rw [hd]
    have hsq : (2 * ε - 1) * (2 * ε - 1) = 1 + 4 * (ε * ε - ε) := by ring
    have hq : Ideal.Quotient.mk I ((2 * ε - 1) * (2 * ε - 1)) = 1 := by
      rw [hsq, map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_left 4 h), add_zero]
    rw [map_mul] at hq
    exact ⟨⟨_, _, hq, hq⟩, rfl⟩
  obtain ⟨a, ha, hae⟩ := HenselianRing.is_henselian (I := I) _ hm ε h0 hu
  refine ⟨a, ?_, hae⟩
  have := ha.eq_zero
  simp only [eval_sub, eval_pow, eval_X] at this
  rw [← pow_two]; exact sub_eq_zero.mp this
end Bl.SecondBlockLemmaI
