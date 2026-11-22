-- Prove2me | solution 1 for BooleanIsoperimetry.distanceToCanonical_zero_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:20.99708+00:00
-- url     : https://prove2.me/submissions/ceb506b4-3f24-4941-9682-123a47f127f7

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_card_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A B : Finset (Cube N))
    (h : distanceToCanonical A B = 0) : IsCanonicalCascadePair A B := by
  have hex : ∃ p q, CascadeSplit N (A.card + B.card) p q := by
    have htot : A.card + B.card ≤ 2 ^ (N + 1) := by
      have := card_le_two_pow A
      have := card_le_two_pow B
      have h2 : (2 : ℕ) ^ (N + 1) = 2 ^ N + 2 ^ N := by ring
      omega
    obtain ⟨p, q, _, _, _, hcs⟩ := exists_cascade_split N (A.card + B.card) htot
    exact ⟨p, q, hcs⟩
  -- unfold the canonical pair on the `dif_pos` branch
  set p := Classical.choose hex with hp
  set q := Classical.choose (Classical.choose_spec hex) with hq
  have hcs : CascadeSplit N (A.card + B.card) p q :=
    Classical.choose_spec (Classical.choose_spec hex)
  have hcanpair : canonicalPairOfTotal N (A.card + B.card)
      = (simplicialInitSeg N p, simplicialInitSeg N q) := by
    unfold canonicalPairOfTotal
    rw [dif_pos hex]
  have hsplit : distanceToCanonical A B
      = (A \ simplicialInitSeg N p).card + (simplicialInitSeg N p \ A).card
        + (B \ simplicialInitSeg N q).card + (simplicialInitSeg N q \ B).card := by
    unfold distanceToCanonical
    rw [hcanpair]
  rw [hsplit] at h
  have hA1 : (A \ simplicialInitSeg N p).card = 0 := by omega
  have hA2 : (simplicialInitSeg N p \ A).card = 0 := by omega
  have hB1 : (B \ simplicialInitSeg N q).card = 0 := by omega
  have hB2 : (simplicialInitSeg N q \ B).card = 0 := by omega
  have hAeq : A = simplicialInitSeg N p := by
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hA1)
    · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hA2)
  have hBeq : B = simplicialInitSeg N q := by
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hB1)
    · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hB2)
  exact ⟨p, q, hcs, hAeq, hBeq⟩
end BooleanIsoperimetry
