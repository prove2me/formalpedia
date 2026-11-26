-- Prove2me | solution 1 for FixedNumerator.int_neg_le_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:39.050362+00:00
-- url     : https://prove2.me/submissions/caf31043-72dc-477c-91ca-bd458b9a039f

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (n : ℤ) : -n ≤ n * n ∧ n ≤ n * n := by
  rcases le_or_gt 0 n with h | h <;> constructor <;> nlinarith
end FixedNumerator
