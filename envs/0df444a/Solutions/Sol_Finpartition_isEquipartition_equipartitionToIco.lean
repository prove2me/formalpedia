-- Prove2me | solution 1 for Finpartition.isEquipartition_equipartitionToIco
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:06.968019+00:00
-- url     : https://prove2.me/submissions/cfe59469-57a1-4e82-941a-c39e8df30252

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Theorems.Thm_Finpartition_card_equipartitionToIco_parts
import Theorems.Thm_Finpartition_card_of_mem_equipartitionToIco_parts_aux

set_option autoImplicit true
open Finset
open Finpartition
namespace Finpartition
theorem _root_.solution {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    (equipartitionToIco a b k).IsEquipartition := by
  rw [isEquipartition_iff_card_parts_eq_average]
  intro i hi
  simp only [Nat.card_Ico, card_equipartitionToIco_parts hk hkn]
  simp only [equipartitionToIco, ne_eq, hk, not_false_eq_true, hkn, and_self, ↓reduceDIte,
    mem_image, mem_range] at hi
  obtain ⟨i, hi, rfl⟩ := hi
  simp only [Nat.card_Ico]
  have := card_of_mem_equipartitionToIco_parts_aux (n := b - a) (k := k) (i := i)
  grind
end Finpartition
