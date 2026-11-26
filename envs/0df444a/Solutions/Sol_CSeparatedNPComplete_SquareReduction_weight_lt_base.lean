-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.weight_lt_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:21.743408+00:00
-- url     : https://prove2.me/submissions/7f2074bf-9ecf-4fa1-8dad-956ede7dca46

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : a i < base a := by
  have h : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  unfold base
  omega
end CSeparatedNPComplete.SquareReduction
