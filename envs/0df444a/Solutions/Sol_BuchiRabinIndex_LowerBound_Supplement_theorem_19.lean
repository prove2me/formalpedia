-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.Supplement.theorem_19
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:15:22.962941+00:00
-- url     : https://prove2.me/submissions/e9e22d51-491b-4b7b-b0fd-998ac14446a6

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Flags
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_13
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_16
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_18
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_lemma_15

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement.Thm19Aux
open BuchiRabinIndex.LowerBound
open BuchiRabinIndex.LowerBound.Supplement
open scoped Classical

lemma weight_le_of_mem_fullTree {n : ℕ} {x : Node} (hx : x ∈ fullTree n) :
    weight x ≤ n - 1 := by
  unfold fullTree at hx
  split_ifs at hx
  · simp at hx
  · exact (Finset.mem_filter.1 hx).2

lemma pos_bw (b : ℕ) : ∀ (d : ℕ) (x : Node), x ∈ boundedWords b d → Positive x
  | 0, x, hx => by
      simp [boundedWords] at hx; subst hx; intro i hi; simp at hi
  | d + 1, x, hx => by
      simp only [boundedWords, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc,
        Finset.mem_image] at hx
      rcases hx with rfl | ⟨j, hj, u, hu, rfl⟩
      · intro i hi; simp at hi
      · intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · omega
        · exact pos_bw b d u hu i hi

lemma pos_of_mem_fullTree (n : ℕ) (x : Node) (hx : x ∈ fullTree n) : Positive x := by
  unfold fullTree at hx
  split_ifs at hx
  · simp at hx
  · exact pos_bw _ _ x (Finset.mem_filter.1 hx).1

lemma sf_eq_zero_of_ge (n w : ℕ) (hn : 1 ≤ n) (hw : n ≤ w) : sf n w = 0 := by
  have hempty : IsEmpty ↥{x : Vertex n | weight x.val = w} := ⟨fun v => by
    have hle := weight_le_of_mem_fullTree v.val.property
    have heq : weight v.val.val = w := v.property
    omega⟩
  have hcol : (weightGraph n w).Colorable 0 :=
    ⟨SimpleGraph.Coloring.mk isEmptyElim (fun {u} => isEmptyElim u)⟩
  have hle : (weightGraph n w).chromaticNumber ≤ (0 : ℕ∞) :=
    (weightGraph n w).chromaticNumber_le_iff_colorable.mpr hcol
  have heq0 : (weightGraph n w).chromaticNumber = 0 := le_bot_iff.mp hle
  unfold sf
  rw [heq0]
  rfl

lemma cf_nil (m : ℕ) : cf (m + 1) [] = 1 := rfl

lemma cf_of_part1 (m : ℕ) {x : Node} (hx : x ∈ part1 (m + 1)) :
    cf (m + 1) x = cf m (phi1 x) := by
  simp only [part1, Finset.mem_image] at hx
  obtain ⟨v, -, rfl⟩ := hx
  rfl

lemma cf_of_part2 (m : ℕ) {x : Node} (hx : x ∈ part2 (m + 1)) :
    cf (m + 1) x =
      if weight x ≤ (m + 1) / 2 then cf m (phi2 x) + 2 ^ (weight x - 2)
      else cf m (phi2 x) := by
  simp only [part2, Finset.mem_image, Finset.mem_erase] at hx
  obtain ⟨u, ⟨hu0, hu⟩, rfl⟩ := hx
  cases u with
  | nil => exact absurd rfl hu0
  | cons i v =>
      have hi : 0 < i := pos_of_mem_fullTree m (i :: v) hu i (by simp)
      have hi0 : i ≠ 0 := by omega
      simp [increment, cf, hi0]

lemma icc_union_shift (K : ℕ) (hK : 1 ≤ K) :
    Finset.Icc 1 K ∪ (Finset.Icc 1 K).image (· + K) = Finset.Icc 1 (2 * K) := by
  ext z
  simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨a, ⟨ha1, ha2⟩, rfl⟩)
    · omega
    · omega
  · rintro ⟨h1, h2⟩
    by_cases hz : z ≤ K
    · exact Or.inl ⟨h1, hz⟩
    · exact Or.inr ⟨z - K, ⟨by omega, by omega⟩, by omega⟩

lemma cf_props : ∀ n, 1 ≤ n →
    (∀ x ∈ fullTree n, ∀ y ∈ fullTree n, x ≠ y → weight x = weight y →
      (chain x ∪ chain y).card ≤ n → cf n x ≠ cf n y) ∧
    (∀ w : ℕ,
      ((fullTree n).filter fun x => weight x = w).image (cf n) =
        Finset.Icc 1 (sf n w))
  | 0, hn => by omega
  | 1, _ => by
      have hf13 := fact_13 1 le_rfl
      have hft1 : fullTree 1 = {[]} := by
        have hsub : {[]} ⊆ fullTree 1 := by
          rw [← hf13.2.1]; exact Finset.filter_subset _ _
        exact (Finset.eq_of_subset_of_card_le hsub (by rw [hf13.1]; simp)).symm
      refine ⟨?_, ?_⟩
      · intro x hx y hy hne
        rw [hft1, Finset.mem_singleton] at hx hy
        exact absurd (hx.trans hy.symm) hne
      · intro w
        by_cases hw0 : w = 0
        · subst hw0
          rw [hf13.2.1, (lemma_15 1 le_rfl).1]
          rfl
        · rw [sf_eq_zero_of_ge 1 w le_rfl (by omega)]
          have hemp : (fullTree 1).filter (fun x => weight x = w) = ∅ := by
            rw [hft1, Finset.filter_eq_empty_iff]
            intro x hx
            rw [Finset.mem_singleton] at hx
            subst hx; simp [weight]; omega
          rw [hemp]
          simp
  | m + 2, _ => by
      let n := m + 2
      have hm1 : 1 ≤ m + 1 := by omega
      have hn2 : 2 ≤ n := by omega
      obtain ⟨ih_dist, ih_img⟩ := cf_props (m + 1) hm1
      obtain ⟨hdecomp, hbij1, hbij2, hw1, hw2⟩ := lemma_16 n hn2
      have hl15 := lemma_15 n (by omega)
      have hl15' := lemma_15 (m + 1) hm1
      have mem_p1_or_p2 : ∀ z ∈ fullTree n, weight z ≠ 0 → z ∈ part1 n ∨ z ∈ part2 n := by
        intro z hz hwz
        have hz' : z ∈ {[]} ∪ part1 n ∪ part2 n := hdecomp ▸ hz
        simp only [Finset.mem_union, Finset.mem_singleton] at hz'
        rcases hz' with (rfl | hp1) | hp2
        · exact absurd rfl hwz
        · exact Or.inl hp1
        · exact Or.inr hp2
      have weight_ge_two_of_part2 : ∀ z ∈ part2 n, 2 ≤ weight z := by
        intro z hz2
        have hm : phi2 z ∈ (fullTree (m + 1)).erase [] := hbij2.mapsTo hz2
        obtain ⟨hm0, hm_ft⟩ := Finset.mem_erase.mp hm
        have hne0 : weight (phi2 z) ≠ 0 := by
          intro h0
          have hmem0 : phi2 z ∈ (fullTree (m + 1)).filter (weight · = 0) :=
            Finset.mem_filter.mpr ⟨hm_ft, h0⟩
          rw [(fact_13 (m + 1) hm1).2.1, Finset.mem_singleton] at hmem0
          exact hm0 hmem0
        have := hw2 z hz2
        omega
      refine ⟨?_, ?_⟩
      · intro x hx y hy hne hweq hcard
        have hl18 := lemma_18 n hn2 x y hx hy hne
        by_cases hwx0 : weight x = 0
        · have hx0 : x ∈ (fullTree n).filter (weight · = 0) := Finset.mem_filter.mpr ⟨hx, hwx0⟩
          have hy0 : y ∈ (fullTree n).filter (weight · = 0) :=
            Finset.mem_filter.mpr ⟨hy, hweq.symm.trans hwx0⟩
          rw [(fact_13 n (by omega)).2.1, Finset.mem_singleton] at hx0 hy0
          exact absurd (hx0.trans hy0.symm) hne
        · have hwy0 : weight y ≠ 0 := hweq ▸ hwx0
          rcases mem_p1_or_p2 x hx hwx0 with hx1 | hx2
          · rcases mem_p1_or_p2 y hy hwy0 with hy1 | hy2
            · rw [cf_of_part1 (m + 1) hx1, cf_of_part1 (m + 1) hy1]
              have hne' : phi1 x ≠ phi1 y := fun h => hne (hbij1.injOn hx1 hy1 h)
              have hw' : weight (phi1 x) = weight (phi1 y) := by
                have := hw1 x hx1; have := hw1 y hy1; omega
              have hc' : (chain (phi1 x) ∪ chain (phi1 y)).card ≤ m + 1 := by
                have := hl18.1 hx1 hy1; omega
              exact ih_dist (phi1 x) (hbij1.mapsTo hx1) (phi1 y) (hbij1.mapsTo hy1) hne' hw' hc'
            · have hw2y := weight_ge_two_of_part2 y hy2
              have hc2w := (hl18.2.2 (Or.inl ⟨hx1, hy2⟩)).2.2 (weight x) rfl hweq.symm
              have hw_half : weight y ≤ n / 2 := by omega
              have hw_sub_half : weight y - 1 ≤ (m + 1) / 2 := by omega
              rw [cf_of_part1 (m + 1) hx1, cf_of_part2 (m + 1) hy2, if_pos hw_half]
              have hx_img : cf (m + 1) (phi1 x) ∈ Finset.Icc 1 (sf (m + 1) (weight y - 1)) := by
                rw [← ih_img (weight y - 1)]
                refine Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hbij1.mapsTo hx1, ?_⟩)
                have := hw1 x hx1; omega
              have hy_img : cf (m + 1) (phi2 y) ∈ Finset.Icc 1 (sf (m + 1) (weight y - 1)) := by
                rw [← ih_img (weight y - 1)]
                refine Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
                  ⟨(Finset.mem_erase.mp (hbij2.mapsTo hy2)).2, ?_⟩)
                have := hw2 y hy2; omega
              rw [hl15'.2.1 (weight y - 1) (by omega) hw_sub_half, Finset.mem_Icc] at hx_img hy_img
              have hpow_eq : weight y - 1 - 1 = weight y - 2 := by omega
              rw [hpow_eq] at hx_img
              omega
          · rcases mem_p1_or_p2 y hy hwy0 with hy1 | hy2
            · have hw2x := weight_ge_two_of_part2 x hx2
              have hc2w := (hl18.2.2 (Or.inr ⟨hx2, hy1⟩)).2.2 (weight x) rfl hweq.symm
              have hw_half : weight x ≤ n / 2 := by omega
              have hw_sub_half : weight x - 1 ≤ (m + 1) / 2 := by omega
              rw [cf_of_part2 (m + 1) hx2, if_pos hw_half, cf_of_part1 (m + 1) hy1]
              have hy_img : cf (m + 1) (phi1 y) ∈ Finset.Icc 1 (sf (m + 1) (weight x - 1)) := by
                rw [← ih_img (weight x - 1)]
                refine Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hbij1.mapsTo hy1, ?_⟩)
                have := hw1 y hy1; omega
              have hx_img : cf (m + 1) (phi2 x) ∈ Finset.Icc 1 (sf (m + 1) (weight x - 1)) := by
                rw [← ih_img (weight x - 1)]
                refine Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
                  ⟨(Finset.mem_erase.mp (hbij2.mapsTo hx2)).2, ?_⟩)
                have := hw2 x hx2; omega
              rw [hl15'.2.1 (weight x - 1) (by omega) hw_sub_half, Finset.mem_Icc] at hx_img hy_img
              have hpow_eq : weight x - 1 - 1 = weight x - 2 := by omega
              rw [hpow_eq] at hy_img
              omega
            · rw [cf_of_part2 (m + 1) hx2, cf_of_part2 (m + 1) hy2, ← hweq]
              have hne' : phi2 x ≠ phi2 y := fun h => hne (hbij2.injOn hx2 hy2 h)
              have hw' : weight (phi2 x) = weight (phi2 y) := by
                have := hw2 x hx2; have := hw2 y hy2; omega
              have hc' : (chain (phi2 x) ∪ chain (phi2 y)).card ≤ m + 1 := by
                have := hl18.2.1 hx2 hy2; omega
              have hdist' := ih_dist (phi2 x) (Finset.mem_erase.mp (hbij2.mapsTo hx2)).2
                (phi2 y) (Finset.mem_erase.mp (hbij2.mapsTo hy2)).2 hne' hw' hc'
              split_ifs
              · omega
              · exact hdist'
      · intro w
        by_cases hw0 : w = 0
        · subst hw0
          rw [(fact_13 n (by omega)).2.1, hl15.1]
          rfl
        · by_cases hwn : n ≤ w
          · rw [sf_eq_zero_of_ge n w (by omega) hwn]
            have hemp : (fullTree n).filter (fun x => weight x = w) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro x hx
              have := weight_le_of_mem_fullTree hx
              omega
            rw [hemp]
            simp
          · by_cases hw_one : w = 1
            · subst hw_one
              rw [hl15.2.1 1 (by omega) (by omega)]
              have hp1_only : (fullTree n).filter (fun x => weight x = 1) =
                  (part1 n).filter (fun x => weight x = 1) := by
                ext x
                simp only [Finset.mem_filter]
                constructor
                · rintro ⟨hx, hwx⟩
                  refine ⟨?_, hwx⟩
                  rcases mem_p1_or_p2 x hx (by omega) with hp1 | hp2
                  · exact hp1
                  · have := weight_ge_two_of_part2 x hp2; omega
                · rintro ⟨hp1, hwx⟩
                  refine ⟨?_, hwx⟩
                  rw [hdecomp]
                  exact Finset.mem_union_left _ (Finset.mem_union_right _ hp1)
              have himg_phi1 : ((part1 n).filter (fun x => weight x = 1)).image phi1 =
                  (fullTree (m + 1)).filter (fun u => weight u = 0) := by
                ext u
                simp only [Finset.mem_image, Finset.mem_filter]
                constructor
                · rintro ⟨x, ⟨hx1, hwx⟩, rfl⟩
                  exact ⟨hbij1.mapsTo hx1, by have := hw1 x hx1; omega⟩
                · rintro ⟨hu, hwu⟩
                  obtain ⟨x, hx1, rfl⟩ := hbij1.surjOn hu
                  exact ⟨x, ⟨hx1, by have := hw1 x hx1; omega⟩, rfl⟩
              have hcomp : ((part1 n).filter (fun x => weight x = 1)).image (cf n) =
                  (((part1 n).filter (fun x => weight x = 1)).image phi1).image (cf (m + 1)) := by
                rw [Finset.image_image]
                refine Finset.image_congr fun x hx => ?_
                exact cf_of_part1 (m + 1) (Finset.mem_filter.mp hx).1
              rw [hp1_only, hcomp, himg_phi1, ih_img 0, hl15'.1]
              simp
            · have hw_ge2 : 2 ≤ w := by omega
              let F1 := (part1 n).filter (fun x => weight x = w)
              let F2 := (part2 n).filter (fun x => weight x = w)
              have hsplit : (fullTree n).filter (fun x => weight x = w) = F1 ∪ F2 := by
                ext x
                simp only [F1, F2, Finset.mem_union, Finset.mem_filter]
                constructor
                · rintro ⟨hx, hwx⟩
                  rcases mem_p1_or_p2 x hx (by omega) with hp1 | hp2
                  · exact Or.inl ⟨hp1, hwx⟩
                  · exact Or.inr ⟨hp2, hwx⟩
                · rintro (⟨hp1, hwx⟩ | ⟨hp2, hwx⟩)
                  · refine ⟨?_, hwx⟩
                    rw [hdecomp]
                    exact Finset.mem_union_left _ (Finset.mem_union_right _ hp1)
                  · refine ⟨?_, hwx⟩
                    rw [hdecomp]
                    exact Finset.mem_union_right _ hp2
              have himg_F1_phi1 : F1.image phi1 =
                  (fullTree (m + 1)).filter (fun u => weight u = w - 1) := by
                ext u
                simp only [F1, Finset.mem_image, Finset.mem_filter]
                constructor
                · rintro ⟨x, ⟨hx1, hwx⟩, rfl⟩
                  exact ⟨hbij1.mapsTo hx1, by have := hw1 x hx1; omega⟩
                · rintro ⟨hu, hwu⟩
                  obtain ⟨x, hx1, rfl⟩ := hbij1.surjOn hu
                  exact ⟨x, ⟨hx1, by have := hw1 x hx1; omega⟩, rfl⟩
              have himg_F2_phi2 : F2.image phi2 =
                  (fullTree (m + 1)).filter (fun u => weight u = w - 1) := by
                ext u
                simp only [F2, Finset.mem_image, Finset.mem_filter]
                constructor
                · rintro ⟨x, ⟨hx2, hwx⟩, rfl⟩
                  exact ⟨(Finset.mem_erase.mp (hbij2.mapsTo hx2)).2,
                    by have := hw2 x hx2; omega⟩
                · rintro ⟨hu, hwu⟩
                  have hu0 : u ≠ [] := by
                    intro h; rw [h] at hwu; simp [weight] at hwu; omega
                  obtain ⟨x, hx2, rfl⟩ := hbij2.surjOn (Finset.mem_erase.mpr ⟨hu0, hu⟩)
                  exact ⟨x, ⟨hx2, by have := hw2 x hx2; omega⟩, rfl⟩
              have himg1 : F1.image (cf n) = Finset.Icc 1 (sf (m + 1) (w - 1)) := by
                rw [← ih_img (w - 1), ← himg_F1_phi1, Finset.image_image]
                exact Finset.image_congr fun x hx =>
                  cf_of_part1 (m + 1) (Finset.mem_filter.mp hx).1
              rw [hsplit, Finset.image_union, himg1]
              by_cases hw_half : w ≤ n / 2
              · have hw_sub_half : w - 1 ≤ (m + 1) / 2 := by omega
                have hsf_prev : sf (m + 1) (w - 1) = 2 ^ (w - 2) :=
                  hl15'.2.1 (w - 1) (by omega) hw_sub_half
                have himg2 : F2.image (cf n) =
                    (Finset.Icc 1 (sf (m + 1) (w - 1))).image (· + 2 ^ (w - 2)) := by
                  rw [← ih_img (w - 1), ← himg_F2_phi2, Finset.image_image, Finset.image_image]
                  refine Finset.image_congr fun x hx => ?_
                  obtain ⟨hx2, hwx⟩ := Finset.mem_filter.mp hx
                  rw [cf_of_part2 (m + 1) hx2, hwx, if_pos hw_half]
                  rfl
                rw [himg2, hsf_prev, hl15.2.1 w (by omega) hw_half,
                  icc_union_shift (2 ^ (w - 2)) (Nat.one_le_pow _ _ (by omega))]
                have h2pow : 2 * 2 ^ (w - 2) = 2 ^ (w - 1) := by
                  conv_rhs => rw [show w - 1 = (w - 2) + 1 by omega]
                  rw [pow_succ]; ring
                rw [h2pow]
              · have himg2 : F2.image (cf n) = Finset.Icc 1 (sf (m + 1) (w - 1)) := by
                  rw [← ih_img (w - 1), ← himg_F2_phi2, Finset.image_image]
                  refine Finset.image_congr fun x hx => ?_
                  obtain ⟨hx2, hwx⟩ := Finset.mem_filter.mp hx
                  rw [cf_of_part2 (m + 1) hx2, hwx, if_neg hw_half]
                  rfl
                rw [himg2, Finset.union_idempotent, hl15.2.2 w (by omega) (by omega)]
                by_cases hsub : w - 1 ≤ (m + 1) / 2
                · rw [hl15'.2.1 (w - 1) (by omega) hsub]
                  congr 2; omega
                · rw [hl15'.2.2 (w - 1) (by omega) (by omega)]
                  congr 2; omega

end BuchiRabinIndex.LowerBound.Supplement.Thm19Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Supplement
  BuchiRabinIndex.LowerBound.Supplement.Thm19Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∀ x ∈ fullTree n, ∀ y ∈ fullTree n, x ≠ y → weight x = weight y →
      (chain x ∪ chain y).card ≤ n → cf n x ≠ cf n y) ∧
    (∀ w : ℕ,
      ((fullTree n).filter fun x => weight x = w).image (cf n) =
        Finset.Icc 1 (sf n w)) :=
  cf_props n hn
