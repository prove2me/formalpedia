-- Prove2me | solution 1 for FixedNumerator.C_sign_even_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:38:12.59732+00:00
-- url     : https://prove2.me/submissions/08588225-e413-4a1a-af6d-19aaa49e77ed

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
public import Theorems.Thm_FixedNumerator_pow_two_mul_sub_one
public import Theorems.Thm_FixedNumerator_norm_sub_mod_eight

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {π : GaussianInt} (hπ : IsPrimary π) (a : GaussianInt) {k : ℕ}
    (hk : Even k) : (-1 : ℂ) ^ C a (π ^ k) = 1 := by
  obtain ⟨j, rfl⟩ := hk
  have h4 : (4 : GaussianInt) ∣ π ^ (j + j) - 1 := by
    rw [← two_mul]; exact pow_two_mul_sub_one hπ j
  have h8 := norm_sub_mod_eight h4
  have hq : (π ^ (j + j)).norm - 1 = 8 * (((π ^ (j + j)).norm - 1) / 8) := by
    simp at h8; omega
  apply Even.neg_one_zpow
  unfold C
  apply Even.mul_left
  rw [Int.even_iff]; omega
end FixedNumerator
