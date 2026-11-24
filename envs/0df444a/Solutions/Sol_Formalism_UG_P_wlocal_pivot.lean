-- Prove2me | solution 1 for Formalism.UG.P.wlocal_pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:55.53537+00:00
-- url     : https://prove2.me/submissions/999c869c-ef24-4fce-8cef-5ce0ea138e9a

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
namespace Formalism.UG.P
theorem _root_.solution {r : ℕ} (k : Fin r) (M N : Matrix (Fin r) (Fin r) R) (hNM : N * M = 1)
    (hstd : ∀ i j : Fin r, j.val < k.val → M i j = if i = j then 1 else 0) :
    ∃ i : Fin r, k.val ≤ i.val ∧ IsUnit (M i k) := by
  by_contra hcon
  push_neg at hcon
  have hNcol : ∀ j : Fin r, j.val < k.val → N k j = 0 := by
    intro j hj
    have h1 : (N * M) k j = 0 := by
      rw [hNM, Matrix.one_apply_ne]
      intro h
      rw [h] at hj
      exact lt_irrefl _ hj
    rw [Matrix.mul_apply] at h1
    have h2 : ∑ l, N k l * M l j = N k j := by
      rw [Finset.sum_eq_single j]
      · rw [hstd j j hj, if_pos rfl, mul_one]
      · intro l _ hl
        rw [hstd l j hj, if_neg hl, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [← h2]
    exact h1
  have hsum : (N * M) k k ∈ IsLocalRing.maximalIdeal R := by
    rw [Matrix.mul_apply]
    apply Ideal.sum_mem
    intro l _
    by_cases hl : l.val < k.val
    · rw [hNcol l hl, zero_mul]
      exact Ideal.zero_mem _
    · apply Ideal.mul_mem_left
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon l (not_lt.mp hl)))
  rw [hNM, Matrix.one_apply_eq] at hsum
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hsum)) isUnit_one
end Formalism.UG.P
