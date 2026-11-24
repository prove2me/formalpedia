-- Prove2me | solution 1 for DeletedPrimes.piS_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:12:07.524831+00:00
-- url     : https://prove2.me/submissions/939641e2-1bf8-4fcf-ab84-2ce8c5839aa9

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {X : ℝ} (hX : 1 ≤ X) :
    piS S (2 * X) = piS S X + intervalCount S X := by
  have h1 : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).mpr hX
  have h2 : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_le_floor (by linarith)
  have hU : Finset.Icc 1 ⌊2 * X⌋₊ = Finset.Icc 1 ⌊X⌋₊ ∪ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hD : Disjoint (Finset.Icc 1 ⌊X⌋₊) (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn hn'
    omega
  unfold piS intervalCount
  rw [hU, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hD)]
end DeletedPrimes
