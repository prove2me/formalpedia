-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.Supplement.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:13:50.57549+00:00
-- url     : https://prove2.me/submissions/7c6510dd-a912-44c7-85f3-71ec8e2b81d0

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Flags
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_13
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_16
import Theorems.Thm_BuchiRabinIndex_LowerBound_corollary_35

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement.Lemma15Aux
open BuchiRabinIndex.LowerBound
open BuchiRabinIndex.LowerBound.Supplement
open scoped Classical

abbrev WVert (n w : ℕ) := ↥{x : Vertex n | weight x.val = w}

lemma wvert_weight {n w : ℕ} (v : WVert n w) : weight v.val.val = w := v.property

lemma pos_bw (b : ℕ) : ∀ (d : ℕ) (x : Node), x ∈ boundedWords b d → Positive x
  | 0, x, hx => by
      simp [boundedWords] at hx
      subst hx
      intro i hi; simp at hi
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

lemma card_chain : ∀ x : Node, Positive x → (chain x).card = weight x + 1
  | [], _ => by simp [chain, weight]
  | i :: v, hx => by
      have hi : 0 < i := hx i (by simp)
      have hv : Positive v := fun k hk => hx k (by simp [hk])
      have ih := card_chain v hv
      have hdisj : Disjoint ((Finset.Icc 1 (i - 1)).image fun j => [j])
          ((chain v).image (i :: ·)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hb
        simp at hy hj; omega
      have hnil : [] ∉ ((Finset.Icc 1 (i - 1)).image fun j => [j]) ∪ ((chain v).image (i :: ·)) := by
        simp
      simp only [chain]
      rw [Finset.card_insert_of_notMem hnil, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun a b h => by simpa using h),
        Finset.card_image_of_injective _ (fun a b h => by simpa using h), ih]
      simp [weight]; omega

lemma card_wvert (n w : ℕ) :
    Fintype.card (WVert n w) = ((fullTree n).filter (weight · = w)).card := by
  let f : WVert n w → ↥((fullTree n).filter (weight · = w)) :=
    fun v => ⟨v.val.val, Finset.mem_filter.mpr ⟨v.val.property, wvert_weight v⟩⟩
  let g : ↥((fullTree n).filter (weight · = w)) → WVert n w :=
    fun u => ⟨⟨u.val, (Finset.mem_filter.mp u.property).1⟩, (Finset.mem_filter.mp u.property).2⟩
  have heq : WVert n w ≃ ↥((fullTree n).filter (weight · = w)) :=
    ⟨f, g, fun _ => rfl, fun _ => rfl⟩
  rw [Fintype.card_congr heq, Fintype.card_coe]

lemma toNat_chromaticNumber_eq {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hcol : G.Colorable k) (hmin : ∀ m : ℕ, G.Colorable m → k ≤ m) :
    G.chromaticNumber.toNat = k := by
  have hle : G.chromaticNumber ≤ (k : ℕ∞) :=
    G.chromaticNumber_le_iff_colorable.mpr hcol
  have hne : G.chromaticNumber ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top k) hle
  let m := G.chromaticNumber.toNat
  have hm_coe : (m : ℕ∞) = G.chromaticNumber := ENat.natCast_toNat hne
  have hm_col : G.Colorable m :=
    G.chromaticNumber_le_iff_colorable.mp (le_of_eq hm_coe.symm)
  have hkm : k ≤ m := hmin m hm_col
  have hmk : m ≤ k := ENat.natCast_le_natCast.mp (hm_coe.trans_le hle)
  omega

lemma sf_eq_card_of_complete (n w : ℕ)
    (hcomp : ∀ u v : WVert n w, u ≠ v → (weightGraph n w).Adj u v) :
    sf n w = ((fullTree n).filter (weight · = w)).card := by
  have hcol : (weightGraph n w).Colorable (Fintype.card (WVert n w)) := by
    let e := Fintype.equivFin (WVert n w)
    exact ⟨SimpleGraph.Coloring.mk e fun {u v} hadj heq => hadj.ne (e.injective heq)⟩
  have hmin : ∀ m : ℕ, (weightGraph n w).Colorable m → Fintype.card (WVert n w) ≤ m := by
    rintro m ⟨C⟩
    have hinj : Function.Injective C := by
      intro u v heq
      by_contra huv
      exact C.valid (hcomp u v huv) heq
    have hc : Fintype.card (WVert n w) ≤ Fintype.card (Fin m) :=
      @Fintype.card_le_of_injective (WVert n w) (Fin m) _ _ C hinj
    rwa [Fintype.card_fin] at hc
  unfold sf
  rw [toNat_chromaticNumber_eq (weightGraph n w) (Fintype.card (WVert n w)) hcol hmin, card_wvert]

lemma sf_zero (n : ℕ) (hn : 1 ≤ n) : sf n 0 = 1 := by
  have hf0 := (fact_13 n hn).2.1
  have hcomp : ∀ u v : WVert n 0, u ≠ v → (weightGraph n 0).Adj u v := by
    intro u v huv
    have hu : u.val.val ∈ (fullTree n).filter (weight · = 0) :=
      Finset.mem_filter.mpr ⟨u.val.property, wvert_weight u⟩
    have hv : v.val.val ∈ (fullTree n).filter (weight · = 0) :=
      Finset.mem_filter.mpr ⟨v.val.property, wvert_weight v⟩
    rw [hf0, Finset.mem_singleton] at hu hv
    exact absurd (Subtype.ext (Subtype.ext (hu.trans hv.symm))) huv
  rw [sf_eq_card_of_complete n 0 hcomp, hf0]
  simp

lemma sf_small (n : ℕ) (hn : 1 ≤ n) (w : ℕ) (hw0 : 0 < w) (hw : w ≤ n / 2) :
    sf n w = 2 ^ (w - 1) := by
  have hcomp : ∀ u v : WVert n w, u ≠ v → (weightGraph n w).Adj u v := by
    intro u v huv
    have hne : u.val.val ≠ v.val.val := fun h => huv (Subtype.ext (Subtype.ext h))
    change Adj n u.val.val v.val.val
    refine ⟨hne, ?_⟩
    have hwu := wvert_weight u
    have hwv := wvert_weight v
    have hu0 : u.val.val ≠ [] := by
      intro h; rw [h] at hwu; simp [weight] at hwu; omega
    have hv0 : v.val.val ≠ [] := by
      intro h; rw [h] at hwv; simp [weight] at hwv; omega
    have pu := pos_of_mem_fullTree n u.val.val u.val.property
    have pv := pos_of_mem_fullTree n v.val.val v.val.property
    have h1u : ({[], [1]} : Finset Node) ⊆ chain u.val.val :=
      (fact_30 u.val.val u.val.val pu pu).2.2.2.2.2.2.2.1 hu0
    have h1v : ({[], [1]} : Finset Node) ⊆ chain v.val.val :=
      (fact_30 v.val.val v.val.val pv pv).2.2.2.2.2.2.2.1 hv0
    have hinter : 2 ≤ (chain u.val.val ∩ chain v.val.val).card := by
      have hc2 : ({[], [1]} : Finset Node).card = 2 := by decide
      rw [← hc2]
      exact Finset.card_le_card (Finset.subset_inter h1u h1v)
    have hcu := Finset.card_union_add_card_inter (chain u.val.val) (chain v.val.val)
    rw [card_chain u.val.val pu, card_chain v.val.val pv, hwu, hwv] at hcu
    omega
  rw [sf_eq_card_of_complete n w hcomp, (fact_13 n hn).2.2 w hw0 (by omega)]

lemma sf_step (n w : ℕ) (hn2 : 2 ≤ n) (hwgt : n / 2 < w) (hwlt : w < n) :
    sf n w = sf (n - 1) (w - 1) := by
  obtain ⟨hdecomp, hbij1, hbij2, hw1, hw2⟩ := lemma_16 n hn2
  have hw_pos : 1 ≤ w := by omega
  have mem_p2_of_not_p1 : ∀ v : WVert n w, v.val.val ∉ part1 n → v.val.val ∈ part2 n := by
    intro v hv1
    have hmem : v.val.val ∈ {[]} ∪ part1 n ∪ part2 n := hdecomp ▸ v.val.property
    simp only [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with (h0 | hp1) | hp2
    · have hwv := wvert_weight v
      rw [h0] at hwv
      simp [weight] at hwv
      omega
    · exact absurd hp1 hv1
    · exact hp2
  let fwd : WVert n w → WVert (n - 1) (w - 1) := fun v =>
    if hv1 : v.val.val ∈ part1 n then
      have hw_p1 : weight (phi1 v.val.val) = w - 1 := by
        have := hw1 v.val.val hv1; have := wvert_weight v; omega
      ⟨⟨phi1 v.val.val, hbij1.mapsTo hv1⟩, hw_p1⟩
    else
      let hv2 := mem_p2_of_not_p1 v hv1
      have hw_p2 : weight (phi2 v.val.val) = w - 1 := by
        have := hw2 v.val.val hv2; have := wvert_weight v; omega
      ⟨⟨phi2 v.val.val, (Finset.mem_erase.mp (hbij2.mapsTo hv2)).2⟩, hw_p2⟩
  let bwd : WVert (n - 1) (w - 1) → WVert n w := fun u =>
    have hp1 : 1 :: u.val.val ∈ part1 n := Finset.mem_image_of_mem _ u.val.property
    have hft : 1 :: u.val.val ∈ fullTree n := by
      rw [hdecomp]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hp1)
    have hw_u : weight (1 :: u.val.val) = w := by
      have huw := wvert_weight u
      simp [weight] at huw ⊢; omega
    ⟨⟨1 :: u.val.val, hft⟩, hw_u⟩
  have hfwd_adj : ∀ u v : WVert n w,
      (weightGraph n w).Adj u v → (weightGraph (n - 1) (w - 1)).Adj (fwd u) (fwd v) := by
    intro u v hadj
    have hadj' : Adj n u.val.val v.val.val := hadj
    have hne : u.val.val ≠ v.val.val := hadj'.1
    have hwu := wvert_weight u
    have hwv := wvert_weight v
    by_cases hu1 : u.val.val ∈ part1 n
    · by_cases hv1 : v.val.val ∈ part1 n
      · simp only [fwd, dif_pos hu1, dif_pos hv1]
        exact ((corollary_35 n hn2 u.val.val v.val.val hne).1 hu1 hv1).mp hadj'
      · have hv2 := mem_p2_of_not_p1 v hv1
        have hsum := ((corollary_35 n hn2 u.val.val v.val.val hne).2.2 hu1 hv2).mp hadj'
        omega
    · have hu2 := mem_p2_of_not_p1 u hu1
      by_cases hv1 : v.val.val ∈ part1 n
      · have hadj_sym : Adj n v.val.val u.val.val :=
          ⟨hne.symm, by simpa [Finset.union_comm] using hadj'.2⟩
        have hsum := ((corollary_35 n hn2 v.val.val u.val.val hne.symm).2.2 hv1 hu2).mp hadj_sym
        omega
      · have hv2 := mem_p2_of_not_p1 v hv1
        simp only [fwd, dif_neg hu1, dif_neg hv1]
        exact ((corollary_35 n hn2 u.val.val v.val.val hne).2.1 hu2 hv2).mp hadj'
  have hbwd_adj : ∀ u v : WVert (n - 1) (w - 1),
      (weightGraph (n - 1) (w - 1)).Adj u v → (weightGraph n w).Adj (bwd u) (bwd v) := by
    intro u v hadj
    have hadj' : Adj (n - 1) u.val.val v.val.val := hadj
    have hne : (1 :: u.val.val) ≠ (1 :: v.val.val) := by simpa using hadj'.1
    have hp1u : 1 :: u.val.val ∈ part1 n := Finset.mem_image_of_mem _ u.val.property
    have hp1v : 1 :: v.val.val ∈ part1 n := Finset.mem_image_of_mem _ v.val.property
    exact ((corollary_35 n hn2 (1 :: u.val.val) (1 :: v.val.val) hne).1 hp1u hp1v).mpr
      (by simpa [phi1] using hadj')
  have hcol_iff : ∀ m : ℕ, (weightGraph n w).Colorable m ↔ (weightGraph (n - 1) (w - 1)).Colorable m := by
    intro m
    constructor
    · rintro ⟨C⟩
      exact ⟨SimpleGraph.Coloring.mk (fun u => C (bwd u)) fun hadj => C.valid (hbwd_adj _ _ hadj)⟩
    · rintro ⟨C⟩
      exact ⟨SimpleGraph.Coloring.mk (fun v => C (fwd v)) fun hadj => C.valid (hfwd_adj _ _ hadj)⟩
  have hex_col : (weightGraph (n - 1) (w - 1)).Colorable (Fintype.card (WVert (n - 1) (w - 1))) := by
    let e := Fintype.equivFin (WVert (n - 1) (w - 1))
    exact ⟨SimpleGraph.Coloring.mk e fun hadj heq => hadj.ne (e.injective heq)⟩
  have hne_top : (weightGraph (n - 1) (w - 1)).chromaticNumber ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _)
      ((weightGraph (n - 1) (w - 1)).chromaticNumber_le_iff_colorable.mpr hex_col)
  let k := sf (n - 1) (w - 1)
  have hk_coe : (k : ℕ∞) = (weightGraph (n - 1) (w - 1)).chromaticNumber :=
    ENat.natCast_toNat hne_top
  have hk_col : (weightGraph n w).Colorable k :=
    (hcol_iff k).mpr ((weightGraph (n - 1) (w - 1)).chromaticNumber_le_iff_colorable.mp
      (le_of_eq hk_coe.symm))
  have hk_min : ∀ m : ℕ, (weightGraph n w).Colorable m → k ≤ m := by
    intro m hm
    have hle := (weightGraph (n - 1) (w - 1)).chromaticNumber_le_iff_colorable.mpr ((hcol_iff m).mp hm)
    exact ENat.natCast_le_natCast.mp (hk_coe.trans_le hle)
  unfold sf
  exact toNat_chromaticNumber_eq (weightGraph n w) k hk_col hk_min

lemma sf_large : ∀ n, 1 ≤ n → ∀ w, n / 2 < w → w < n → sf n w = 2 ^ (n - w - 1)
  | 0, hn => by omega
  | 1, _ => by intro w hw1 hw2; omega
  | m + 2, _ => by
      intro w hwgt hwlt
      rw [sf_step (m + 2) w (by omega) hwgt hwlt]
      change sf (m + 1) (w - 1) = 2 ^ (m + 2 - w - 1)
      by_cases hle : w - 1 ≤ (m + 1) / 2
      · rw [sf_small (m + 1) (by omega) (w - 1) (by omega) hle]
        congr 1; omega
      · rw [sf_large (m + 1) (by omega) (w - 1) (by omega) (by omega)]
        congr 1; omega

end BuchiRabinIndex.LowerBound.Supplement.Lemma15Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Supplement
  BuchiRabinIndex.LowerBound.Supplement.Lemma15Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    sf n 0 = 1 ∧
    (∀ w : ℕ, 0 < w → w ≤ n / 2 → sf n w = 2 ^ (w - 1)) ∧
    (∀ w : ℕ, n / 2 < w → w < n → sf n w = 2 ^ (n - w - 1)) :=
  ⟨sf_zero n hn, sf_small n hn, sf_large n hn⟩
