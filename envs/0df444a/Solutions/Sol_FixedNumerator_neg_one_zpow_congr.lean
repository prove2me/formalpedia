-- Prove2me | solution 1 for FixedNumerator.neg_one_zpow_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:10.11299+00:00
-- url     : https://prove2.me/submissions/40933b3a-fb5e-4776-ac97-26451663ac9d

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {m n : ℤ} (h : m % 2 = n % 2) : (-1 : ℂ) ^ m = (-1 : ℂ) ^ n := by
  rcases Int.emod_two_eq_zero_or_one m with hm | hm
  · rw [Even.neg_one_zpow (Int.even_iff.mpr hm), Even.neg_one_zpow (Int.even_iff.mpr (h ▸ hm))]
  · rw [Odd.neg_one_zpow (Int.odd_iff.mpr hm), Odd.neg_one_zpow (Int.odd_iff.mpr (h ▸ hm))]
end FixedNumerator
