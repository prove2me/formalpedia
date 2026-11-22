-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_split_reaches_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:01.192497+00:00
-- url     : https://prove2.me/submissions/320a3256-a0c6-4d3d-b141-e1fdbf929cb8

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
public import Theorems.Thm_BooleanIsoperimetry_embeddedPair_card
public import Theorems.Thm_BooleanIsoperimetry_embeddedPair_eq_of_slice_eq
public import Theorems.Thm_BooleanIsoperimetry_PairShadowCost_initSeg_eq_max_H
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_embeddedPair_initSeg_card
public import Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_neighborhood_card_min
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split
public import Theorems.Thm_BooleanIsoperimetry_slice0_initSeg_eq
public import Theorems.Thm_BooleanIsoperimetry_slice1_initSeg_eq
public import Theorems.Thm_BooleanIsoperimetry_slice_card_eq_cascade


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (a b : ℕ)
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    ∃ A' B' : Finset (Cube N), IsCanonicalCascadePair A' B' ∧
      A'.card + B'.card = a + b ∧
      PairShadowCost N A' B'
        ≤ PairShadowCost N (simplicialInitSeg N a) (simplicialInitSeg N b) := by
  have htot : a + b ≤ 2 ^ (N + 1) := by
    have h2 : (2 : ℕ) ^ (N + 1) = 2 ^ N + 2 ^ N := by ring
    omega
  obtain ⟨p, q, hp, hq, hsum, hcasc⟩ := exists_cascade_split N (a + b) htot
  use simplicialInitSeg N p, simplicialInitSeg N q
  have hpcard : (simplicialInitSeg N p).card = p := by
    rw [card_simplicialInitSeg, min_eq_left hp]
  have hqcard : (simplicialInitSeg N q).card = q := by
    rw [card_simplicialInitSeg, min_eq_left hq]
  constructor
  · exact ⟨p, q, by rw [hpcard, hqcard, hsum]; exact hcasc, rfl, rfl⟩
  · constructor
    · rw [hpcard, hqcard]
      exact hsum
    · let A := simplicialInitSeg N a
      let B := simplicialInitSeg N b
      let F := embeddedPair N A B
      have hFcard : F.card = a + b := by
        rw [embeddedPair_card, card_simplicialInitSeg, card_simplicialInitSeg]
        · rw [min_eq_left ha, min_eq_left hb]
      have hF_nbhd : PairShadowCost N A B = (neighborhood 1 F).card := by
        rw [PairShadowCost_initSeg_eq_max_H ha hb]
        exact (neighborhood_embeddedPair_initSeg_card ha hb).symm
      let P := simplicialInitSeg N p
      let Q := simplicialInitSeg N q
      let C := embeddedPair N P Q
      have hC_is_init : C = simplicialInitSeg (N + 1) (a + b) := by
        symm
        apply embeddedPair_eq_of_slice_eq
        · rw [slice0_initSeg_eq]
          have h0card := (slice_card_eq_cascade hcasc).1
          rw [h0card]
        · rw [slice1_initSeg_eq]
          have h1card := (slice_card_eq_cascade hcasc).2
          rw [h1card]
      have hC_nbhd : PairShadowCost N P Q = (neighborhood 1 C).card := by
        rw [PairShadowCost_initSeg_eq_max_H hp hq]
        exact (neighborhood_embeddedPair_initSeg_card hp hq).symm
      have h_min := simplicialInitSeg_neighborhood_card_min F
      rw [hFcard] at h_min
      rw [← hC_is_init] at h_min
      rw [hF_nbhd, hC_nbhd]
      exact h_min
end BooleanIsoperimetry
