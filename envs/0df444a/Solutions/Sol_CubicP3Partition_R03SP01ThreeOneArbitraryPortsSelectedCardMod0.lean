-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeOneArbitraryPortsSelectedCardMod0
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:21:53.684264+00:00
-- url     : https://prove2.me/submissions/d2320667-f206-4e26-976a-9b307b0c79da

import Mathlib

namespace CubicP3Partition

open scoped Nat

/-- The selected indices and residual intervals in the d ≡ 0 row cover one
    complete cyclic order without overlap.  The intervals are represented as
    ordinary natural-number intervals after choosing port 0 as origin. -/
theorem R03SP01ThreeOneArbitraryPortsIndexCoverageMod0
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 0) :
    ({0, 1, d - 1, d} ∪ Finset.Icc 2 (d - 2) ∪
      Finset.Icc (d + 1) ((1 + 3 * b) - 1)) = Finset.range (1 + 3 * b) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_Icc, Finset.mem_range]
  have hmod : d % 3 < 3 := Nat.mod_lt _ (by omega)
  omega

/-- The selected indices and residual intervals in the d ≡ 1 row cover one
    complete cyclic order without overlap. -/
theorem R03SP01ThreeOneArbitraryPortsIndexCoverageMod1
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 1) :
    ({0, d, d + 1, (1 + 3 * b) - 1} ∪ Finset.Icc 1 (d - 1) ∪
      Finset.Icc (d + 2) ((1 + 3 * b) - 2)) = Finset.range (1 + 3 * b) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_Icc, Finset.mem_range]
  have hmod : d % 3 < 3 := Nat.mod_lt _ (by omega)
  omega

/-- The selected indices and residual intervals in the d ≡ 2 row cover one
    complete cyclic order without overlap. -/
theorem R03SP01ThreeOneArbitraryPortsIndexCoverageMod2
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 2) :
    ({0, 1, d, d + 1} ∪ Finset.Icc 2 (d - 1) ∪
      Finset.Icc (d + 2) ((1 + 3 * b) - 1)) = Finset.range (1 + 3 * b) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_Icc, Finset.mem_range]
  have hmod : d % 3 < 3 := Nat.mod_lt _ (by omega)
  omega


end CubicP3Partition

open CubicP3Partition
open scoped Nat
theorem solution
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 0) :
    ({0, 1, d - 1, d} : Finset Nat).card = 4 := by
  have hmod : d % 3 < 3 := Nat.mod_lt _ (by omega)
  have h0 : (0 : Nat) ∉ ({1, d - 1, d} : Finset Nat) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have h1 : (1 : Nat) ∉ ({d - 1, d} : Finset Nat) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hm1 : d - 1 ∉ ({d} : Finset Nat) := by
    simp only [Finset.mem_singleton]
    omega
  rw [Finset.card_insert_of_notMem h0,
    Finset.card_insert_of_notMem h1,
    Finset.card_insert_of_notMem hm1]
  simp

