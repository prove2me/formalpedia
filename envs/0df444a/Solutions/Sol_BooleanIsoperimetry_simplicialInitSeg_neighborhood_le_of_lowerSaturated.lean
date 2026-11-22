-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialInitSeg_neighborhood_le_of_lowerSaturated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:03.702277+00:00
-- url     : https://prove2.me/submissions/90b8a838-51fc-4279-9bc4-36b53e7b2595

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
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_card_le_of_layers_upperShadow_le
public import Theorems.Thm_BooleanIsoperimetry_upperLayerShadow_eq_filter_layer
public import Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_zero
public import Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_one
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_eq_card_lt
public import Theorems.Thm_BooleanIsoperimetry_card_le_choose_of_uniform
public import Theorems.Thm_BooleanIsoperimetry_layerInitSeg_uniform
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_binomPrefix_iff
public import Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_decomp
public import Theorems.Thm_BooleanIsoperimetry_upperLayerShadow_min
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)}
    (hl : IsLowerLevelSaturated A) :
    (neighborhood 1 (simplicialInitSeg N A.card)).card ≤ (neighborhood 1 A).card := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [simplicialInitSeg_zero]
  · set r := (A.image Finset.card).max' (hne.image Finset.card) with hr_def
    -- membership witness of the top layer
    have hrmem : r ∈ A.image Finset.card := Finset.max'_mem _ _
    obtain ⟨w0, hw0A, hw0card⟩ := Finset.mem_image.mp hrmem
    have hA_le : ∀ w ∈ A, w.card ≤ r := fun w hw =>
      Finset.le_max' _ _ (Finset.mem_image_of_mem _ hw)
    have hA_full : ∀ z : Cube N, z.card < r → z ∈ A := by
      intro z hz; exact hl (by rw [hw0card]; exact hz) hw0A
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · -- r = 0 : A = {∅}, initial segment equals A
      have hAeq : A = {(∅ : Cube N)} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨?_, ?_⟩
        · have h0 : w0.card = 0 := by rw [hw0card, hr0]
          have : w0 = (∅ : Cube N) := Finset.card_eq_zero.mp h0
          exact this ▸ hw0A
        · intro x hx
          have : x.card ≤ 0 := by rw [← hr0]; exact hA_le x hx
          exact Finset.card_eq_zero.mp (Nat.le_zero.mp this)
      rw [hAeq]
      have : ({(∅ : Cube N)} : Finset (Cube N)).card = 1 := Finset.card_singleton _
      rw [this, simplicialInitSeg_one]
    · -- r ≥ 1 : the KK jump
      set L := A.filter (fun z => z.card = r) with hL_def
      have hL : ∀ x ∈ L, x.card = r := fun x hx => (Finset.mem_filter.mp hx).2
      set t := L.card with ht_def
      have ht_choose : t ≤ Nat.choose N r := card_le_choose_of_uniform hL
      -- A splits as (full ball below r) ∪ L
      have hAeq : A = (Finset.univ.filter (fun z : Cube N => z.card < r)) ∪ L := by
        ext z
        simp only [hL_def, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hz
          rcases lt_or_eq_of_le (hA_le z hz) with h | h
          · exact Or.inl h
          · exact Or.inr ⟨hz, h⟩
        · rintro (h | ⟨hz, _⟩)
          · exact hA_full z h
          · exact hz
      have hdisj : Disjoint (Finset.univ.filter (fun z : Cube N => z.card < r)) L := by
        rw [Finset.disjoint_left]; intro z hz hzL
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        have := (Finset.mem_filter.mp hzL).2; omega
      have hAcard : A.card = binomPrefix N r + t := by
        rw [hAeq, Finset.card_union_of_disjoint hdisj, ← binomPrefix_eq_card_lt, ht_def]
      -- the initial segment
      set IS := simplicialInitSeg N A.card with hIS_def
      have hlow : simplicialInitSeg N (binomPrefix N r) =
          Finset.univ.filter (fun z : Cube N => z.card < r) := by
        ext z
        simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and,
          rank_lt_binomPrefix_iff]
      have hIS_eq : IS = (Finset.univ.filter (fun z : Cube N => z.card < r))
          ∪ layerInitSeg N r t := by
        rw [hIS_def, hAcard, simplicialInitSeg_decomp ht_choose, hlow]
      -- L1 hypotheses for A' = IS
      have hIS_le : ∀ w ∈ IS, w.card ≤ r := by
        intro w hw; rw [hIS_eq] at hw
        rcases Finset.mem_union.mp hw with h | h
        · exact le_of_lt (Finset.mem_filter.mp h).2
        · exact le_of_eq (layerInitSeg_uniform w h)
      have hIS_full : ∀ z : Cube N, z.card < r → z ∈ IS := by
        intro z hz; rw [hIS_eq]
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
      have hIS_slice : IS.filter (fun z => z.card = r) = layerInitSeg N r t := by
        ext z
        constructor
        · intro hz
          rcases Finset.mem_filter.mp hz with ⟨hzIS, hzc⟩
          rw [hIS_eq] at hzIS
          rcases Finset.mem_union.mp hzIS with h | h
          · exact absurd (Finset.mem_filter.mp h).2 (by omega)
          · exact h
        · intro hz
          refine Finset.mem_filter.mpr ⟨?_, layerInitSeg_uniform z hz⟩
          rw [hIS_eq]; exact Finset.mem_union_right _ hz
      have h_shadow : (upperLayerShadow N r IS).card ≤ (upperLayerShadow N r A).card := by
        rw [upperLayerShadow_eq_filter_layer IS, upperLayerShadow_eq_filter_layer A,
          hIS_slice, ← hL_def]
        have hmin := upperLayerShadow_min hL
        rwa [← ht_def] at hmin
      have := neighborhood_card_le_of_layers_upperShadow_le hrpos hA_le hIS_le hA_full
        hIS_full h_shadow
      rw [hIS_def] at this
      exact this
end BooleanIsoperimetry
