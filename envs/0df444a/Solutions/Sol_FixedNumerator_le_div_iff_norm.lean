-- Prove2me | solution 1 for FixedNumerator.le_div_iff_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:26.709963+00:00
-- url     : https://prove2.me/submissions/851c2fff-2491-4bd2-8390-31e7e9ae338c

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
public import Theorems.Thm_FixedNumerator_toNat_norm

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {X M : ℕ} (hM : 0 < M) (c : GaussianInt) :
    c.norm ≤ ((X / M : ℕ) : ℤ) ↔ (M : ℤ) * c.norm ≤ X := by
  rw [← toNat_norm c]
  norm_cast
  rw [Nat.le_div_iff_mul_le hM, mul_comm]
end FixedNumerator
