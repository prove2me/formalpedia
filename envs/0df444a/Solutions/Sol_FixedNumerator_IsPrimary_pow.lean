-- Prove2me | solution 1 for FixedNumerator.IsPrimary.pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:36:45.26745+00:00
-- url     : https://prove2.me/submissions/ee48c090-596e-4124-92a5-000303366965

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
public import Theorems.Thm_FixedNumerator_IsPrimary_mul

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
namespace IsPrimary
theorem _root_.solution {a : GaussianInt} (ha : IsPrimary a) (k : ℕ) : IsPrimary (a ^ k) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih => rw [pow_succ]; exact ih.mul ha
end IsPrimary
end FixedNumerator
