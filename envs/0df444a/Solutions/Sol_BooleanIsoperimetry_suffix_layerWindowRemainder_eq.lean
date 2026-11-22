-- Prove2me | solution 1 for BooleanIsoperimetry.suffix_layerWindowRemainder_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:41.191995+00:00
-- url     : https://prove2.me/submissions/2b548d4a-770d-4d6f-b62b-136d45c16f05

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_sum_Ico_layerCount_eq_filter_card_ge
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_binomPrefix_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N m k : ℕ) (hm : m ≤ 2 ^ N) :
    ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r m
      = m - binomPrefix N k := by
  -- By definition of `layerWindowRemainder`, the sum is the cardinality of the set of
  -- elements in the initial segment with rank at least `binomPrefix N k`.
  have h_card : ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r m =
      (simplicialInitSeg N m \ simplicialInitSeg N (min m (binomPrefix N k))).card := by
    have hsum :
        ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r m =
          ((simplicialInitSeg N m).filter (fun x => k ≤ x.card)).card := by
      simpa [layerWindowRemainder] using
        sum_Ico_layerCount_eq_filter_card_ge N k (simplicialInitSeg N m)
    have hfilter :
        (simplicialInitSeg N m).filter (fun x => k ≤ x.card) =
          simplicialInitSeg N m \ simplicialInitSeg N (min m (binomPrefix N k)) := by
      ext x
      simp only [simplicialInitSeg, mem_filter, mem_univ, true_and, mem_sdiff]
      constructor
      · rintro ⟨hrank, hcard⟩
        refine ⟨hrank, ?_⟩
        intro hmin
        have hrank_binom : rank x < binomPrefix N k := lt_of_lt_of_le hmin (min_le_right _ _)
        have hcard_lt : x.card < k :=
          (rank_lt_binomPrefix_iff (n := N) (c := k) x).mp hrank_binom
        omega
      · rintro ⟨hrank, hnot⟩
        refine ⟨hrank, ?_⟩
        exact Nat.le_of_not_lt fun hcard_lt =>
          hnot (lt_min hrank ((rank_lt_binomPrefix_iff (n := N) (c := k) x).mpr hcard_lt))
    rw [hsum, hfilter]
  rw [h_card, Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr, card_simplicialInitSeg, card_simplicialInitSeg]
  · grind
  · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1,
      lt_of_lt_of_le (Finset.mem_filter.mp hx |>.2) (min_le_left _ _) ⟩
end BooleanIsoperimetry
