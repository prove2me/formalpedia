-- Prove2me | solution 1 for Finpartition.card_of_mem_equipartitionToIco_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:00.622731+00:00
-- url     : https://prove2.me/submissions/9324d56a-9337-4f83-937d-ee6d8e800859

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Theorems.Thm_Finpartition_card_of_mem_equipartitionToIco_parts_aux

set_option autoImplicit true
open Finset
open Finpartition
namespace Finpartition
theorem _root_.solution
    {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a)
    (i : Finset ℕ) (hi : i ∈ (equipartitionToIco a b k).parts) :
    #i = (b - a) / k ∨ #i = (b - a) / k + 1 := by
  simp only [equipartitionToIco, ne_eq, hk, not_false_eq_true, hkn, and_self, ↓reduceDIte,
    mem_image, mem_range] at hi
  obtain ⟨i, hi, rfl⟩ := hi
  simp only [Nat.card_Ico]
  have := card_of_mem_equipartitionToIco_parts_aux (n := b - a) (k := k) (i := i)
  grind
end Finpartition
