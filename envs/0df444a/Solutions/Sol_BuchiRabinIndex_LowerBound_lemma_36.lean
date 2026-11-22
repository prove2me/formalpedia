-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_36
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:10:42.756876+00:00
-- url     : https://prove2.me/submissions/ec067204-e313-4e4e-b93a-3ad53ef2e748

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_13
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_16
import Theorems.Thm_BuchiRabinIndex_LowerBound_corollary_35

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Lemma36Aux
open BuchiRabinIndex.LowerBound

section ClassicalPart
noncomputable section
open scoped Classical

lemma pos_bw (b : ℕ) : ∀ (d : ℕ) (x : Node), x ∈ boundedWords b d → Positive x
  | 0, x, hx => by
      simp [boundedWords] at hx
      subst hx
      intro i hi
      simp at hi
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

lemma weight_le_of_mem_fullTree {n : ℕ} {x : Node} (hx : x ∈ fullTree n) :
    weight x ≤ n - 1 := by
  unfold fullTree at hx
  split_ifs at hx
  · simp at hx
  · exact (Finset.mem_filter.1 hx).2

lemma nil_mem_boundedWords (b : ℕ) : ∀ d : ℕ, [] ∈ boundedWords b d
  | 0 => by simp [boundedWords]
  | d + 1 => by simp [boundedWords]

lemma nil_mem_fullTree {n : ℕ} (hn : 1 ≤ n) : [] ∈ fullTree n := by
  have hn0 : n ≠ 0 := by omega
  unfold fullTree
  rw [if_neg hn0, Finset.mem_filter]
  exact ⟨nil_mem_boundedWords (n - 1) (n - 1), by simp [weight]⟩

lemma nil_mem_chain (x : Node) : [] ∈ chain x := by
  cases x with
  | nil => simp [chain]
  | cons i v => simp [chain]

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

lemma adj_symm {n : ℕ} {x y : Node} (h : Adj n x y) : Adj n y x :=
  ⟨h.1.symm, by simpa [Finset.union_comm] using h.2⟩

lemma adj_nil_left {n : ℕ} (hn : 1 ≤ n) {x : Node} (hx : x ∈ fullTree n) (hne : [] ≠ x) :
    Adj n [] x := by
  refine ⟨hne, ?_⟩
  have hunion : chain [] ∪ chain x = chain x := by
    ext z
    simp only [chain, Finset.singleton_union, Finset.mem_insert]
    exact ⟨fun h => h.elim (fun hz => hz ▸ nil_mem_chain x) id, Or.inr⟩
  rw [hunion, card_chain x (pos_of_mem_fullTree n x hx)]
  have hw := weight_le_of_mem_fullTree hx
  omega

lemma adj_nil_right {n : ℕ} (hn : 1 ≤ n) {x : Node} (hx : x ∈ fullTree n) (hne : x ≠ []) :
    Adj n x [] :=
  adj_symm (adj_nil_left hn hx hne.symm)

def ValidClique (n c : ℕ) (S : Finset Node) : Prop :=
  S ⊆ fullTree n ∧ (∀ x ∈ S, weight x ≤ c) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Adj n x y

def cliqueFinset (n c : ℕ) : Finset (Finset Node) :=
  (fullTree n).powerset.filter fun (S : Finset Node) =>
    (∀ x ∈ S, weight x ≤ c) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Adj n x y

lemma mem_cliqueFinset {n c : ℕ} {S : Finset Node} :
    S ∈ cliqueFinset n c ↔ ValidClique n c S := by
  simp only [cliqueFinset, ValidClique, Finset.mem_filter, Finset.mem_powerset]

lemma le_g_of_valid {n c : ℕ} {S : Finset Node} (h : ValidClique n c S) :
    S.card ≤ g n c := by
  change S.card ≤ (cliqueFinset n c).sup Finset.card
  exact Finset.le_sup (f := Finset.card) (mem_cliqueFinset.mpr h)

lemma exists_max_clique (n c : ℕ) : ∃ S, ValidClique n c S ∧ S.card = g n c := by
  have hempty : ∅ ∈ cliqueFinset n c := by
    rw [mem_cliqueFinset]
    exact ⟨Finset.empty_subset _, by simp, by simp⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (cliqueFinset n c) Finset.card ⟨∅, hempty⟩
  refine ⟨S, mem_cliqueFinset.mp hS, le_antisymm (le_g_of_valid (mem_cliqueFinset.mp hS)) ?_⟩
  change (cliqueFinset n c).sup Finset.card ≤ S.card
  exact Finset.sup_le fun T hT => hmax T hT

lemma validClique_insert_nil {n c : ℕ} (hn : 1 ≤ n) {S : Finset Node}
    (hS : ValidClique n c S) : ValidClique n c (insert [] S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact nil_mem_fullTree hn
    · exact hS.1 hxS
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · simp [weight]
    · exact hS.2.1 x hxS
  · intro x hx y hy hne
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · rcases Finset.mem_insert.mp hy with rfl | hyS
      · exact absurd rfl hne
      · exact adj_nil_left hn (hS.1 hyS) hne
    · rcases Finset.mem_insert.mp hy with rfl | hyS
      · exact adj_nil_right hn (hS.1 hxS) hne
      · exact hS.2.2 x hxS y hyS hne

lemma nil_mem_of_max {n c : ℕ} (hn : 1 ≤ n) {S : Finset Node}
    (hS : ValidClique n c S) (hcard : S.card = g n c) : [] ∈ S := by
  by_contra hnot
  have hv := validClique_insert_nil hn hS
  have hle := le_g_of_valid hv
  rw [Finset.card_insert_of_notMem hnot, hcard] at hle
  omega

lemma sum_pow_levels : ∀ c : ℕ,
    ∑ w ∈ Finset.range (c + 1), (if w = 0 then 1 else 2 ^ (w - 1)) = 2 ^ c
  | 0 => by simp
  | c + 1 => by
      rw [Finset.sum_range_succ, sum_pow_levels c]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      omega

lemma card_weight_le (n c : ℕ) (hn : 1 ≤ n) (hc : c ≤ n - 1) :
    ((fullTree n).filter (weight · ≤ c)).card = 2 ^ c := by
  let W := (fullTree n).filter (weight · ≤ c)
  have hmap : ∀ x ∈ W, weight x ∈ Finset.range (c + 1) := by
    intro x hx
    have hxc := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_range]; omega
  rw [Finset.card_eq_sum_card_fiberwise hmap, ← sum_pow_levels c]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_range] at hw
  have hfib : W.filter (fun x => weight x = w) = (fullTree n).filter (weight · = w) := by
    ext x
    simp only [W, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, _⟩, rfl⟩; exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩; exact ⟨⟨hx, by omega⟩, rfl⟩
  rw [hfib]
  have hf13 := fact_13 n hn
  split_ifs with hw0
  · subst hw0
    rw [hf13.2.1]
    simp
  · exact hf13.2.2 w (by omega) (by omega)

lemma part_a (n : ℕ) (hn : 1 ≤ n) (c : ℕ) (hc : c ≤ n / 2) : g n c = 2 ^ c := by
  let W := (fullTree n).filter (weight · ≤ c)
  have hc' : c ≤ n - 1 := by omega
  have hWcard : W.card = 2 ^ c := card_weight_le n c hn hc'
  have hWvalid : ValidClique n c W := by
    refine ⟨Finset.filter_subset _ _, fun x hx => (Finset.mem_filter.mp hx).2, ?_⟩
    intro x hx y hy hne
    obtain ⟨hxT, hxw⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyT, hyw⟩ := Finset.mem_filter.mp hy
    by_cases hx0 : x = []
    · subst hx0; exact adj_nil_left hn hyT hne
    · by_cases hy0 : y = []
      · subst hy0; exact adj_nil_right hn hxT hne
      · refine ⟨hne, ?_⟩
        have px := pos_of_mem_fullTree n x hxT
        have py := pos_of_mem_fullTree n y hyT
        have h1x : ({[], [1]} : Finset Node) ⊆ chain x :=
          (fact_30 x x px px).2.2.2.2.2.2.2.1 hx0
        have h1y : ({[], [1]} : Finset Node) ⊆ chain y :=
          (fact_30 y y py py).2.2.2.2.2.2.2.1 hy0
        have hinter : 2 ≤ (chain x ∩ chain y).card := by
          have hc2 : ({[], [1]} : Finset Node).card = 2 := by decide
          rw [← hc2]
          exact Finset.card_le_card (Finset.subset_inter h1x h1y)
        have hcu := Finset.card_union_add_card_inter (chain x) (chain y)
        rw [card_chain x px, card_chain y py] at hcu
        omega
  apply le_antisymm
  · rw [← hWcard]
    change (cliqueFinset n c).sup Finset.card ≤ W.card
    refine Finset.sup_le fun S hS => Finset.card_le_card fun x hx => ?_
    have hv := mem_cliqueFinset.mp hS
    exact Finset.mem_filter.mpr ⟨hv.1 hx, hv.2.1 x hx⟩
  · rw [← hWcard]
    exact le_g_of_valid hWvalid

lemma nil_notMem_part1 (n : ℕ) : [] ∉ part1 n := by
  simp [part1]

lemma nil_notMem_part2 (n : ℕ) : [] ∉ part2 n := by
  simp only [part2, Finset.mem_image, Finset.mem_erase]
  rintro ⟨u, ⟨hu0, _⟩, hu⟩
  cases u with
  | nil => exact hu0 rfl
  | cons i v => simp [increment] at hu

lemma disjoint_part1_part2 (n : ℕ) : Disjoint (part1 n) (part2 n) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [part1, Finset.mem_image] at hx1
  simp only [part2, Finset.mem_image, Finset.mem_erase] at hx2
  obtain ⟨v, -, rfl⟩ := hx1
  obtain ⟨u, ⟨hu0, hu⟩, heq⟩ := hx2
  cases u with
  | nil => exact hu0 rfl
  | cons i w =>
      have hi : 0 < i := pos_of_mem_fullTree (n - 1) (i :: w) hu i (by simp)
      simp [increment] at heq
      omega

lemma inc_inj : Function.Injective increment := by
  intro a b h
  cases a <;> cases b <;> simp_all [increment]

lemma phi2_inc_of_ne_nil {u : Node} (hu0 : u ≠ []) : phi2 (increment u) = u := by
  cases u with
  | nil => exact absurd rfl hu0
  | cons i v => simp [increment, phi2]

lemma weight_inc_of_ne_nil {u : Node} (hu0 : u ≠ []) : weight (increment u) = weight u + 1 := by
  cases u with
  | nil => exact absurd rfl hu0
  | cons i v => simp [increment, weight]; omega

end
end ClassicalPart

lemma part_b (n : ℕ) (hn2 : 2 ≤ n) (c : ℕ) (hc1 : 1 ≤ c) (hcn : c ≤ n - 1) :
    g n c = (((Finset.range c).product (Finset.range c)).filter
      (fun ab => ab.1 + ab.2 ≤ n - 2)).sup
        (fun ab => g (n - 1) ab.1 + g (n - 1) ab.2) := by
  obtain ⟨hdecomp, hbij1, hbij2, hw1, hw2⟩ := lemma_16 n hn2
  apply le_antisymm
  · obtain ⟨S, hS, hScard⟩ := exists_max_clique n c
    have hnilS : [] ∈ S := nil_mem_of_max (by omega) hS hScard
    let S1 := S ∩ part1 n
    let S2 := S ∩ part2 n
    have hS_eq : S = insert [] (S1 ∪ S2) := by
      ext x
      simp only [S1, S2, Finset.mem_insert, Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        have hxT : x ∈ {[]} ∪ part1 n ∪ part2 n := hdecomp ▸ hS.1 hx
        simp only [Finset.mem_union, Finset.mem_singleton] at hxT
        rcases hxT with (rfl | hp1) | hp2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hx, hp1⟩)
        · exact Or.inr (Or.inr ⟨hx, hp2⟩)
      · rintro (rfl | ⟨hx, -⟩ | ⟨hx, -⟩)
        · exact hnilS
        · exact hx
        · exact hx
    have hnil12 : [] ∉ S1 ∪ S2 := by
      simp only [S1, S2, Finset.mem_union, Finset.mem_inter, not_or, not_and]
      exact ⟨fun _ => nil_notMem_part1 n, fun _ => nil_notMem_part2 n⟩
    have hdisj12 : Disjoint S1 S2 :=
      Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (disjoint_part1_part2 n)
    have hcard_split : S.card = 1 + S1.card + S2.card := by
      rw [hS_eq, Finset.card_insert_of_notMem hnil12, Finset.card_union_of_disjoint hdisj12]
      omega
    let A := S1.image phi1
    let B0 := S2.image phi2
    let B := insert [] B0
    have hAcard : A.card = S1.card := by
      refine Finset.card_image_of_injOn ?_
      exact hbij1.injOn.mono fun x hx => (Finset.mem_inter.mp hx).2
    have hB0card : B0.card = S2.card := by
      refine Finset.card_image_of_injOn ?_
      exact hbij2.injOn.mono fun x hx => (Finset.mem_inter.mp hx).2
    have hnilB0 : [] ∉ B0 := by
      simp only [B0, Finset.mem_image]
      rintro ⟨y, hy, hphi⟩
      have hy2 : y ∈ part2 n := (Finset.mem_inter.mp hy).2
      have hmem : phi2 y ∈ (fullTree (n - 1)).erase [] := hbij2.mapsTo hy2
      exact (Finset.mem_erase.mp hmem).1 hphi
    have hBcard : B.card = 1 + S2.card := by
      rw [Finset.card_insert_of_notMem hnilB0, hB0card]; omega
    have hABcard : S.card = A.card + B.card := by
      rw [hcard_split, hAcard, hBcard]; omega
    let a := A.sup weight
    let b := B.sup weight
    have ha_le : a ≤ c - 1 := by
      refine Finset.sup_le fun u hu => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨hxS, hx1⟩ := Finset.mem_inter.mp hx
      have := hS.2.1 x hxS
      have := hw1 x hx1
      omega
    have hb_le : b ≤ c - 1 := by
      refine Finset.sup_le fun u hu => ?_
      rcases Finset.mem_insert.mp hu with rfl | hu0
      · simp [weight]
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu0
        obtain ⟨hyS, hy2⟩ := Finset.mem_inter.mp hy
        have := hS.2.1 y hyS
        have := hw2 y hy2
        omega
    have hab_le : a + b ≤ n - 2 := by
      by_cases hS1e : S1 = ∅
      · have hAe : A = ∅ := by simp [A, hS1e]
        have ha0 : a = 0 := by simp [a, hAe]
        omega
      · by_cases hS2e : S2 = ∅
        · have hB0e : B0 = ∅ := by simp [B0, hS2e]
          have hb0 : b = 0 := by simp [b, B, hB0e, weight]
          omega
        · have hAne : A.Nonempty := (Finset.nonempty_of_ne_empty hS1e).image phi1
          have hB0ne : B0.Nonempty := (Finset.nonempty_of_ne_empty hS2e).image phi2
          obtain ⟨u1, hu1A, hu1max⟩ := Finset.exists_max_image A weight hAne
          obtain ⟨u2, hu2B0, hu2max⟩ := Finset.exists_max_image B0 weight hB0ne
          have ha_eq : a = weight u1 :=
            le_antisymm (Finset.sup_le hu1max) (Finset.le_sup (f := weight) hu1A)
          have hb_eq : b = weight u2 := by
            apply le_antisymm
            · refine Finset.sup_le fun z hz => ?_
              rcases Finset.mem_insert.mp hz with rfl | hz0
              · simp [weight]
              · exact hu2max z hz0
            · exact Finset.le_sup (f := weight) (Finset.mem_insert_of_mem hu2B0)
          obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.mp hu1A
          obtain ⟨x2, hx2, rfl⟩ := Finset.mem_image.mp hu2B0
          obtain ⟨hx1S, hx1P⟩ := Finset.mem_inter.mp hx1
          obtain ⟨hx2S, hx2P⟩ := Finset.mem_inter.mp hx2
          have hne12 : x1 ≠ x2 := fun h =>
            Finset.disjoint_left.mp (disjoint_part1_part2 n) hx1P (h ▸ hx2P)
          have hadj := hS.2.2 x1 hx1S x2 hx2S hne12
          have hsum := ((corollary_35 n hn2 x1 x2 hne12).2.2 hx1P hx2P).mp hadj
          have hwx1 := hw1 x1 hx1P
          have hwx2 := hw2 x2 hx2P
          omega
    have hAvalid : ValidClique (n - 1) a A := by
      refine ⟨?_, fun u hu => Finset.le_sup (f := weight) hu, ?_⟩
      · intro u hu
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        exact hbij1.mapsTo (Finset.mem_inter.mp hx).2
      · intro u hu v hv huv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
        have hxy : x ≠ y := fun h => huv (h ▸ rfl)
        obtain ⟨hxS, hx1⟩ := Finset.mem_inter.mp hx
        obtain ⟨hyS, hy1⟩ := Finset.mem_inter.mp hy
        exact ((corollary_35 n hn2 x y hxy).1 hx1 hy1).mp (hS.2.2 x hxS y hyS hxy)
    have hB0valid : ValidClique (n - 1) b B0 := by
      refine ⟨?_, fun u hu => Finset.le_sup (f := weight) (Finset.mem_insert_of_mem hu), ?_⟩
      · intro u hu
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        have hm : phi2 x ∈ (fullTree (n - 1)).erase [] := hbij2.mapsTo (Finset.mem_inter.mp hx).2
        exact (Finset.mem_erase.mp hm).2
      · intro u hu v hv huv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
        have hxy : x ≠ y := fun h => huv (h ▸ rfl)
        obtain ⟨hxS, hx2⟩ := Finset.mem_inter.mp hx
        obtain ⟨hyS, hy2⟩ := Finset.mem_inter.mp hy
        exact ((corollary_35 n hn2 x y hxy).2.1 hx2 hy2).mp (hS.2.2 x hxS y hyS hxy)
    have hBvalid : ValidClique (n - 1) b B := validClique_insert_nil (by omega) hB0valid
    have hmemIdx : (a, b) ∈ ((Finset.range c).product (Finset.range c)).filter
        (fun ab => ab.1 + ab.2 ≤ n - 2) := by
      simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, hab_le⟩
    calc g n c
        = S.card := hScard.symm
      _ = A.card + B.card := hABcard
      _ ≤ g (n - 1) a + g (n - 1) b := Nat.add_le_add (le_g_of_valid hAvalid) (le_g_of_valid hBvalid)
      _ ≤ (((Finset.range c).product (Finset.range c)).filter
            (fun ab => ab.1 + ab.2 ≤ n - 2)).sup (fun ab => g (n - 1) ab.1 + g (n - 1) ab.2) :=
          Finset.le_sup (f := fun ab : ℕ × ℕ => g (n - 1) ab.1 + g (n - 1) ab.2) (b := (a, b)) hmemIdx
  · refine Finset.sup_le fun ab hab => ?_
    rcases ab with ⟨a, b⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hab
    obtain ⟨⟨ha_lt, hb_lt⟩, hab_le⟩ := hab
    obtain ⟨A, hA, hAcard⟩ := exists_max_clique (n - 1) a
    obtain ⟨B, hB, hBcard⟩ := exists_max_clique (n - 1) b
    have hnilB : [] ∈ B := nil_mem_of_max (by omega) hB hBcard
    let B' := B.erase []
    have hB'card : B'.card + 1 = B.card := Finset.card_erase_add_one hnilB
    let S1 := A.image (1 :: ·)
    let S2 := B'.image increment
    let S := insert [] (S1 ∪ S2)
    have hS1sub : S1 ⊆ part1 n := Finset.image_subset_image hA.1
    have hS2sub : S2 ⊆ part2 n := by
      refine Finset.image_subset_image ?_
      intro u hu
      obtain ⟨hu0, huB⟩ := Finset.mem_erase.mp hu
      exact Finset.mem_erase.mpr ⟨hu0, hB.1 huB⟩
    have hnil12 : [] ∉ S1 ∪ S2 := by
      simp only [Finset.mem_union, not_or]
      exact ⟨fun h => nil_notMem_part1 n (hS1sub h), fun h => nil_notMem_part2 n (hS2sub h)⟩
    have hdisj12 : Disjoint S1 S2 :=
      Disjoint.mono hS1sub hS2sub (disjoint_part1_part2 n)
    have hS1card : S1.card = A.card :=
      Finset.card_image_of_injective A fun u v h => by simpa using h
    have hS2card : S2.card = B'.card :=
      Finset.card_image_of_injective B' inc_inj
    have hScard : S.card = g (n - 1) a + g (n - 1) b := by
      rw [Finset.card_insert_of_notMem hnil12, Finset.card_union_of_disjoint hdisj12,
        hS1card, hS2card, hAcard]
      omega
    have hS12valid : ValidClique n c (S1 ∪ S2) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [hdecomp]
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hS1sub hx1))
        · exact Finset.mem_union_right _ (hS2sub hx2)
      · intro x hx
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx1
          have := hA.2.1 u hu
          simp [weight] at *; omega
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx2
          obtain ⟨hu0, huB⟩ := Finset.mem_erase.mp hu
          have := hB.2.1 u huB
          rw [weight_inc_of_ne_nil hu0]; omega
      · intro x hx y hy hne
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · rcases Finset.mem_union.mp hy with hy1 | hy2
          · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx1
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy1
            have huv : u ≠ v := fun h => hne (by rw [h])
            exact ((corollary_35 n hn2 (1 :: u) (1 :: v) hne).1 (hS1sub hx1) (hS1sub hy1)).mpr
              (by simpa [phi1] using hA.2.2 u hu v hv huv)
          · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx1
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy2
            obtain ⟨hv0, hvB⟩ := Finset.mem_erase.mp hv
            have hwu := hA.2.1 u hu
            have hwv := hB.2.1 v hvB
            refine ((corollary_35 n hn2 (1 :: u) (increment v) hne).2.2 (hS1sub hx1) (hS2sub hy2)).mpr ?_
            rw [weight_inc_of_ne_nil hv0]
            simp [weight] at *; omega
        · rcases Finset.mem_union.mp hy with hy1 | hy2
          · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx2
            obtain ⟨hu0, huB⟩ := Finset.mem_erase.mp hu
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy1
            have hwu := hB.2.1 u huB
            have hwv := hA.2.1 v hv
            refine adj_symm (((corollary_35 n hn2 (1 :: v) (increment u) hne.symm).2.2
              (hS1sub hy1) (hS2sub hx2)).mpr ?_)
            rw [weight_inc_of_ne_nil hu0]
            simp [weight] at *; omega
          · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx2
            obtain ⟨hu0, huB⟩ := Finset.mem_erase.mp hu
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy2
            obtain ⟨hv0, hvB⟩ := Finset.mem_erase.mp hv
            have huv : u ≠ v := fun h => hne (by rw [h])
            refine ((corollary_35 n hn2 (increment u) (increment v) hne).2.1
              (hS2sub hx2) (hS2sub hy2)).mpr ?_
            rw [phi2_inc_of_ne_nil hu0, phi2_inc_of_ne_nil hv0]
            exact hB.2.2 u huB v hvB huv
    have hSvalid : ValidClique n c S := validClique_insert_nil (by omega) hS12valid
    rw [← hScard]
    exact le_g_of_valid hSvalid

end BuchiRabinIndex.LowerBound.Lemma36Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Lemma36Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∀ c, c ≤ n / 2 → g n c = 2 ^ c) ∧
    (2 ≤ n → ∀ c, 1 ≤ c → c ≤ n - 1 →
      g n c = (((Finset.range c).product (Finset.range c)).filter
        (fun ab => ab.1 + ab.2 ≤ n - 2)).sup
          (fun ab => g (n - 1) ab.1 + g (n - 1) ab.2)) :=
  ⟨part_a n hn, part_b n⟩
