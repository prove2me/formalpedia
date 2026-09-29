-- Prove2me | solution 1 for BraidsLinksMCG.artin_action_trivial_perm
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T20:38:07.241478+00:00
-- url     : https://prove2.me/submissions/1c51e2d5-cf43-43ad-ac82-7a6e90f4b9df

import Theorems.Thm_BraidsLinksMCG_artin_action_conj_perm
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace TrivPerm

/-- In a free group, conjugate generators are equal. -/
theorem of_eq_conj_of {α : Type*} [DecidableEq α] {j k : α} {A : FreeGroup α}
    (h : FreeGroup.of j = A * FreeGroup.of k * A⁻¹) : j = k := by
  by_contra hne
  set phi : FreeGroup α →* Multiplicative ℤ :=
    FreeGroup.lift (fun m => if m = j then Multiplicative.ofAdd (1 : ℤ) else 1) with hphi
  have h1 : phi (FreeGroup.of j) = Multiplicative.ofAdd (1 : ℤ) := by
    rw [hphi]; simp
  have h3 : phi (FreeGroup.of k) = 1 := by
    rw [hphi]; simp [if_neg (Ne.symm hne)]
  have h2 : phi (A * FreeGroup.of k * A⁻¹) = phi (FreeGroup.of k) := by
    rw [map_mul, map_mul, map_inv, mul_comm (phi A) (phi (FreeGroup.of k)),
      mul_assoc, mul_inv_cancel, mul_one]
  rw [h, h2, h3] at h1
  exact absurd h1.symm (by simp)

end TrivPerm

theorem _root_.solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i))
    (b : ArtinBraidGroup n) (hb : xi b = 1) : pi b = 1 := by
  apply Equiv.ext
  intro j
  obtain ⟨A, hA⟩ := BraidsLinksMCG.artin_action_conj_perm n xi hxi pi hpi b j
  rw [hb] at hA
  have h : FreeGroup.of j = A * FreeGroup.of (pi b j) * A⁻¹ := hA
  exact (TrivPerm.of_eq_conj_of h).symm

#print axioms solution
