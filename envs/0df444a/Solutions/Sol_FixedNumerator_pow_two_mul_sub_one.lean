-- Prove2me | solution 1 for FixedNumerator.pow_two_mul_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:36:31.533444+00:00
-- url     : https://prove2.me/submissions/d7b48b42-dc24-4c06-80e0-a18ac6df77e3

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
public import Theorems.Thm_FixedNumerator_sq_sub_one

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {π : GaussianInt} (hπ : IsPrimary π) (k : ℕ) :
    (4 : GaussianInt) ∣ π ^ (2 * k) - 1 := by
  rw [pow_mul]
  exact dvd_trans (sq_sub_one hπ) (sub_one_dvd_pow_sub_one _ k)
end FixedNumerator
