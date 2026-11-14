-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.card_cover_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:43.975073+00:00
-- url     : https://prove2.me/submissions/2fc10770-8120-474c-96be-818027555d1f

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream

theorem solution {k m : ℕ} (S : Finset (Fin (k + m * k))) (j : ℕ)
    (hj : ∀ e ∈ S, k ≤ e.val → (e.val - k) / k < j) :
    (S.biUnion (gridStreamCover k m)).card ≤
      rowsHeld k S * k + columnsHeld k S * (k - rowsHeld k S) + columnsHeld k S * j := by
  classical
  set Rs : Finset ℕ := (S.filter fun e => e.val < k).image Fin.val with hRs
  set Is : Finset ℕ := (S.filter fun e => k ≤ e.val).image fun e => (e.val - k) % k with hIs
  have hRcard : Rs.card = rowsHeld k S := card_image_of_injective _ Fin.val_injective
  have hIcard : Is.card ≤ columnsHeld k S := card_image_le
  have hRsub : Rs ⊆ range k := by
    intro r hr
    obtain ⟨e, he, rfl⟩ := mem_image.mp hr
    exact mem_range.mpr (mem_filter.mp he).2
  have hsub : (S.biUnion (gridStreamCover k m)).map Fin.valEmbedding ⊆
      ((Rs ×ˢ range k).image fun p => p.1 * k + p.2) ∪
        (((range k \ Rs) ×ˢ Is).image fun p => p.1 * k + p.2) ∪
        ((Is ×ˢ range j).image fun p => k * k + p.1 * m + p.2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    obtain ⟨e, he, hxe⟩ := mem_biUnion.mp hx
    simp only [gridStreamCover, mem_filter, mem_univ, true_and] at hxe
    simp only [Fin.valEmbedding_apply]
    split_ifs at hxe with hrow
    · -- a cell of the row `a_{e+1}`
      obtain ⟨_, hdiv⟩ := hxe
      have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hrow
      refine mem_union_left _ (mem_union_left _ (mem_image.mpr
        ⟨(x.val / k, x.val % k), mem_product.mpr ⟨?_, mem_range.mpr (Nat.mod_lt _ hk)⟩,
          Nat.div_add_mod' x.val k⟩))
      rw [hdiv]
      exact mem_image.mpr ⟨e, mem_filter.mpr ⟨he, hrow⟩, rfl⟩
    · have hi : (e.val - k) % k ∈ Is :=
        mem_image.mpr ⟨e, mem_filter.mpr ⟨he, by omega⟩, rfl⟩
      rcases hxe with ⟨hxk, hmod⟩ | ⟨hxk, hdiv, hlt⟩
      · -- a grid cell of the column of `e`, inside a held row or not
        have hk : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · subst h
            simp at hxk
          · exact h
        have hr : x.val / k < k := (Nat.div_lt_iff_lt_mul hk).mpr hxk
        by_cases hrR : x.val / k ∈ Rs
        · exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨(x.val / k, x.val % k),
            mem_product.mpr ⟨hrR, mem_range.mpr (Nat.mod_lt _ hk)⟩, Nat.div_add_mod' x.val k⟩))
        · refine mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨(x.val / k, x.val % k),
            mem_product.mpr ⟨mem_sdiff.mpr ⟨mem_range.mpr hr, hrR⟩, ?_⟩,
              Nat.div_add_mod' x.val k⟩))
          rw [hmod]
          exact hi
      · -- an auxiliary element `u_{i,l+1}` with `l ≤ (e - k) / k < j`
        refine mem_union_right _ (mem_image.mpr ⟨((x.val - k * k) / m, (x.val - k * k) % m),
          mem_product.mpr ⟨by rw [hdiv]; exact hi, mem_range.mpr ?_⟩, ?_⟩)
        · exact lt_of_le_of_lt hlt (hj e he (by omega))
        · have := Nat.div_add_mod' (x.val - k * k) m
          simp only
          omega
  have hprod1 : ((Rs ×ˢ range k).image fun p => p.1 * k + p.2).card ≤ Rs.card * k := by
    refine card_image_le.trans ?_
    rw [card_product, card_range]
  have hprod2 : (((range k \ Rs) ×ˢ Is).image fun p => p.1 * k + p.2).card ≤
      (k - Rs.card) * Is.card := by
    refine card_image_le.trans ?_
    rw [card_product, card_sdiff_of_subset hRsub, card_range]
  have hprod3 : ((Is ×ˢ range j).image fun p => k * k + p.1 * m + p.2).card ≤ Is.card * j := by
    refine card_image_le.trans ?_
    rw [card_product, card_range]
  have hunion : (((Rs ×ˢ range k).image fun p => p.1 * k + p.2) ∪
        (((range k \ Rs) ×ˢ Is).image fun p => p.1 * k + p.2) ∪
        ((Is ×ˢ range j).image fun p => k * k + p.1 * m + p.2)).card ≤
      ((Rs ×ˢ range k).image fun p => p.1 * k + p.2).card +
        (((range k \ Rs) ×ˢ Is).image fun p => p.1 * k + p.2).card +
        ((Is ×ˢ range j).image fun p => k * k + p.1 * m + p.2).card :=
    (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  have hmain := (card_le_card hsub).trans hunion
  rw [card_map] at hmain
  rw [hRcard] at hprod1 hprod2
  have h2 : (k - rowsHeld k S) * Is.card ≤ columnsHeld k S * (k - rowsHeld k S) := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ hIcard
  have h3 : Is.card * j ≤ columnsHeld k S * j := Nat.mul_le_mul_right _ hIcard
  omega

end
