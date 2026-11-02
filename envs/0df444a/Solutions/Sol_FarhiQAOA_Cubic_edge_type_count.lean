-- Prove2me | solution 1 for FarhiQAOA.Cubic.edge_type_count
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:54:12.650868+00:00
-- url     : https://prove2.me/submissions/62e80605-e6d4-4bf5-b62e-8ec5c35d9beb

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic.EdgeTypeCountAux

open QAlgorithms FarhiQAOA.Cubic

def bipSum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Y : Finset (Fin n)) : ℕ :=
  ∑ u ∈ X, (Y.filter (G.Adj u)).card

lemma bipSum_union_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {X₁ X₂ : Finset (Fin n)} (Y : Finset (Fin n)) (h : Disjoint X₁ X₂) :
    bipSum G (X₁ ∪ X₂) Y = bipSum G X₁ Y + bipSum G X₂ Y :=
  Finset.sum_union h

lemma bipSum_union_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X : Finset (Fin n)) {Y₁ Y₂ : Finset (Fin n)} (h : Disjoint Y₁ Y₂) :
    bipSum G X (Y₁ ∪ Y₂) = bipSum G X Y₁ + bipSum G X Y₂ := by
  simp only [bipSum, Finset.filter_union]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact Finset.card_union_of_disjoint (h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

lemma bipSum_comm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Y : Finset (Fin n)) :
    bipSum G X Y = bipSum G Y X := by
  simp only [bipSum, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [G.adj_comm]

lemma bipSum_union_self {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {A B : Finset (Fin n)} (h : Disjoint A B) :
    bipSum G (A ∪ B) (A ∪ B) = bipSum G A A + 2 * bipSum G A B + bipSum G B B := by
  rw [bipSum_union_left G _ h, bipSum_union_right G A h, bipSum_union_right G B h,
    bipSum_comm G B A]
  ring

lemma card_univ_filter_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (u : Fin n) :
    (Finset.univ.filter (G.Adj u)).card = 3 := by
  have hdeg : Finset.univ.filter (G.Adj u) = G.neighborFinset u := by
    ext v; simp [SimpleGraph.mem_neighborFinset]
  rw [hdeg, SimpleGraph.card_neighborFinset_eq_degree, h3 u]

lemma card_filter_add_card_compl_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (X : Finset (Fin n)) (u : Fin n) :
    (X.filter (G.Adj u)).card + (Xᶜ.filter (G.Adj u)).card = 3 := by
  have hd : Disjoint (X.filter (G.Adj u)) (Xᶜ.filter (G.Adj u)) :=
    disjoint_compl_right.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hu : X.filter (G.Adj u) ∪ Xᶜ.filter (G.Adj u) = Finset.univ.filter (G.Adj u) := by
    rw [← Finset.filter_union, Finset.union_compl]
  rw [← Finset.card_union_of_disjoint hd, hu, card_univ_filter_adj G h3 u]

lemma bipSum_univ_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (X : Finset (Fin n)) :
    bipSum G X Finset.univ = 3 * X.card := by
  have hcard : ∀ u ∈ X, (Finset.univ.filter (G.Adj u)).card = 3 :=
    fun u _ => card_univ_filter_adj G h3 u
  simp only [bipSum]
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]

lemma bipSum_le_three_mul_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (X Y : Finset (Fin n)) :
    bipSum G X Y ≤ 3 * X.card := by
  rw [← bipSum_univ_right G h3 X]
  refine Finset.sum_le_sum fun u _ => ?_
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ Y))

lemma bipSum_self_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X : Finset (Fin n)) :
    bipSum G X X ≤ X.card * (X.card - 1) := by
  have hle : ∀ u ∈ X, (X.filter (G.Adj u)).card ≤ X.card - 1 := by
    intro u hu
    have hsub : X.filter (G.Adj u) ⊆ X.erase u := by
      intro v hv
      rw [Finset.mem_filter] at hv
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hv.2).symm, hv.1⟩
    calc (X.filter (G.Adj u)).card ≤ (X.erase u).card := Finset.card_le_card hsub
      _ = X.card - 1 := Finset.card_erase_of_mem hu
  calc bipSum G X X ≤ ∑ _u ∈ X, (X.card - 1) := Finset.sum_le_sum hle
    _ = X.card * (X.card - 1) := by simp

lemma bipSum_singleton_self {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    bipSum G {u} {u} = 0 := by
  have := bipSum_self_le G {u}
  simp at this
  exact this

lemma bipSum_self_eq_two_mul_edgesWithin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X : Finset (Fin n)) :
    bipSum G X X = 2 * (edgesWithin G X).card := by
  have h1 : bipSum G X X = ((X ×ˢ X).filter fun e => G.Adj e.1 e.2).card := by
    simp only [bipSum, Finset.card_filter, Finset.sum_product]
  rw [h1]
  let s1 := (X ×ˢ X).filter fun e => e.1 < e.2 ∧ G.Adj e.1 e.2
  let s2 := (X ×ˢ X).filter fun e => e.2 < e.1 ∧ G.Adj e.1 e.2
  have hsplit : ((X ×ˢ X).filter fun e => G.Adj e.1 e.2) = s1 ∪ s2 := by
    ext ⟨u, v⟩
    simp only [s1, s2, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨huv, hadj⟩
      rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
      · left; exact ⟨huv, hlt, hadj⟩
      · right; exact ⟨huv, hgt, hadj⟩
    · rintro (⟨huv, _, hadj⟩ | ⟨huv, _, hadj⟩) <;> exact ⟨huv, hadj⟩
  have hdisj : Disjoint s1 s2 := by
    rw [Finset.disjoint_left]
    intro ⟨u, v⟩ h1 h2
    simp only [s1, s2, Finset.mem_filter] at h1 h2
    exact lt_asymm h1.2.1 h2.2.1
  have hswap : s2.card = s1.card := by
    refine Finset.card_bij (fun e _ => Prod.swap e) ?_ ?_ ?_
    · intro ⟨u, v⟩ h
      simp only [s1, s2, Finset.mem_filter, Finset.mem_product, Prod.swap] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2.1, h.2.2.symm⟩
    · intro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h
      exact Prod.swap_injective h
    · intro ⟨u, v⟩ h
      refine ⟨(v, u), ?_, rfl⟩
      simp only [s1, s2, Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2.1, h.2.2.symm⟩
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hswap, two_mul]
  rfl

lemma bipSum_of_mem_crossedSquares {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Q : Finset (Fin n)} (hQ : Q ∈ crossedSquares G) :
    Q.card = 4 ∧ bipSum G Q Q = 10 := by
  simp only [crossedSquares, Finset.mem_filter, Finset.mem_powersetCard] at hQ
  refine ⟨hQ.1.2, ?_⟩
  rw [bipSum_self_eq_two_mul_edgesWithin, hQ.2]

lemma bipSum_of_spansClique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {R : Finset (Fin n)} (hcard : R.card = 3) (hclique : SpansClique G R) :
    bipSum G R R = 6 ∧ (edgesWithin G R).card = 3 := by
  have hdeg : ∀ u ∈ R, (R.filter (G.Adj u)).card = 2 := by
    intro u hu
    have heq : R.filter (G.Adj u) = R.erase u := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hv, hadj⟩
        exact ⟨(G.ne_of_adj hadj).symm, hv⟩
      · rintro ⟨hne, hv⟩
        exact ⟨hv, hclique u hu v hv hne.symm⟩
    rw [heq, Finset.card_erase_of_mem hu, hcard]
  have hb : bipSum G R R = 6 := by
    simp only [bipSum]
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hcard]
    rfl
  have he := bipSum_self_eq_two_mul_edgesWithin G R
  exact ⟨hb, by omega⟩

lemma bipSum_of_mem_isolatedTriangles {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {R : Finset (Fin n)} (hR : R ∈ isolatedTriangles G) :
    R.card = 3 ∧ bipSum G R R = 6 ∧ SpansClique G R ∧ LeavingEndsDistinct G R ∧
      (edgesWithin G R).card = 3 := by
  simp only [isolatedTriangles, Finset.mem_filter, Finset.mem_powersetCard] at hR
  obtain ⟨hb, he⟩ := bipSum_of_spansClique hR.1.2 hR.2.1
  exact ⟨hR.1.2, hb, hR.2.1, hR.2.2, he⟩

lemma master_ineq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (X Y : Finset (Fin n)) :
    bipSum G X X + bipSum G Y Y ≤
      6 * (X ∩ Y).card + (X \ Y).card * ((X \ Y).card - 1) + (Y \ X).card * ((Y \ X).card - 1) ∧
    bipSum G X X = bipSum G (X ∩ Y) (X ∩ Y) + 2 * bipSum G (X ∩ Y) (X \ Y) + bipSum G (X \ Y) (X \ Y) ∧
    bipSum G Y Y = bipSum G (X ∩ Y) (X ∩ Y) + 2 * bipSum G (X ∩ Y) (Y \ X) + bipSum G (Y \ X) (Y \ X) := by
  set I := X ∩ Y
  set A := X \ Y
  set B := Y \ X
  have hdIA : Disjoint I A := by
    rw [Finset.disjoint_left]; intro x hx1 hx2; simp [I, A] at hx1 hx2; tauto
  have hdIB : Disjoint I B := by
    rw [Finset.disjoint_left]; intro x hx1 hx2; simp [I, B] at hx1 hx2; tauto
  have hdAB : Disjoint A B := by
    rw [Finset.disjoint_left]; intro x hx1 hx2; simp [A, B] at hx1 hx2; tauto
  have hX : I ∪ A = X := by ext x; simp [I, A]; tauto
  have hY : I ∪ B = Y := by ext x; simp [I, B]; tauto
  have hXX : bipSum G X X = bipSum G I I + 2 * bipSum G I A + bipSum G A A := by
    rw [← hX, bipSum_union_self G hdIA]
  have hYY : bipSum G Y Y = bipSum G I I + 2 * bipSum G I B + bipSum G B B := by
    rw [← hY, bipSum_union_self G hdIB]
  have hdI_AB : Disjoint I (A ∪ B) := Finset.disjoint_union_right.mpr ⟨hdIA, hdIB⟩
  have hsumI : bipSum G I I + bipSum G I A + bipSum G I B ≤ 3 * I.card := by
    have : bipSum G I I + (bipSum G I A + bipSum G I B) = bipSum G I (I ∪ (A ∪ B)) := by
      rw [bipSum_union_right G I hdI_AB, bipSum_union_right G I hdAB]
    linarith [bipSum_le_three_mul_card G h3 I (I ∪ (A ∪ B))]
  have hAA := bipSum_self_le G A
  have hBB := bipSum_self_le G B
  refine ⟨by linarith, hXX, hYY⟩

lemma not_two_adj_outside_of_leavingEndsDistinct {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {R I : Finset (Fin n)} (hR : LeavingEndsDistinct G R) (hIR : I ⊆ R)
    {S : Finset (Fin n)} (hSR : Disjoint S R) (hScard : S.card = 1)
    (hbip : 2 ≤ bipSum G I S) : False := by
  rw [bipSum_comm] at hbip
  obtain ⟨d, rfl⟩ := Finset.card_eq_one.mp hScard
  simp only [bipSum, Finset.sum_singleton] at hbip
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hbip
  simp only [Finset.mem_filter] at hu hv
  have hdR : d ∈ Rᶜ := by
    rw [Finset.mem_compl]
    exact Finset.disjoint_singleton_left.mp hSR
  exact hR u (hIR hu.1) v (hIR hv.1) huv d hdR d hdR hu.2.symm hv.2.symm rfl

lemma disjoint_crossedSquares {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {Q₁ Q₂ : Finset (Fin n)}
    (h1 : Q₁ ∈ crossedSquares G) (h2 : Q₂ ∈ crossedSquares G) (hne : Q₁ ≠ Q₂) :
    Disjoint Q₁ Q₂ := by
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
  obtain ⟨hc1, hb1⟩ := bipSum_of_mem_crossedSquares h1
  obtain ⟨hc2, hb2⟩ := bipSum_of_mem_crossedSquares h2
  have ⟨hm, _, _⟩ := master_ineq G h3 Q₁ Q₂
  have hcs1 := Finset.card_inter_add_card_sdiff Q₁ Q₂
  have hcs2 := Finset.card_inter_add_card_sdiff Q₂ Q₁
  rw [Finset.inter_comm] at hcs2
  have hcard1 : (Q₁ \ Q₂).card = 4 - (Q₁ ∩ Q₂).card := by omega
  have hcard2 : (Q₂ \ Q₁).card = 4 - (Q₁ ∩ Q₂).card := by omega
  have hlt4 : (Q₁ ∩ Q₂).card ≠ 4 := by
    intro h4
    apply hne
    have heq1 : Q₁ ∩ Q₂ = Q₁ := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have heq2 : Q₁ ∩ Q₂ = Q₂ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact heq1.symm.trans heq2
  rw [hb1, hb2, hcard1, hcard2] at hm
  set k := (Q₁ ∩ Q₂).card with hk
  have hk_le : k ≤ 4 := by omega
  interval_cases k <;> omega

lemma disjoint_isolatedTriangles {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {R₁ R₂ : Finset (Fin n)}
    (h1 : R₁ ∈ isolatedTriangles G) (h2 : R₂ ∈ isolatedTriangles G) (hne : R₁ ≠ R₂) :
    Disjoint R₁ R₂ := by
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
  obtain ⟨hc1, hb1, _, hled1, _⟩ := bipSum_of_mem_isolatedTriangles h1
  obtain ⟨hc2, hb2, _, _, _⟩ := bipSum_of_mem_isolatedTriangles h2
  have ⟨hm, _, hYY⟩ := master_ineq G h3 R₁ R₂
  have hcs1 := Finset.card_inter_add_card_sdiff R₁ R₂
  have hcs2 := Finset.card_inter_add_card_sdiff R₂ R₁
  rw [Finset.inter_comm] at hcs2
  have hcard1 : (R₁ \ R₂).card = 3 - (R₁ ∩ R₂).card := by omega
  have hcard2 : (R₂ \ R₁).card = 3 - (R₁ ∩ R₂).card := by omega
  have hlt3 : (R₁ ∩ R₂).card ≠ 3 := by
    intro h3c
    apply hne
    have heq1 : R₁ ∩ R₂ = R₁ := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have heq2 : R₁ ∩ R₂ = R₂ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact heq1.symm.trans heq2
  rw [hb1, hb2, hcard1, hcard2] at hm
  rw [hb2] at hYY
  set k := (R₁ ∩ R₂).card with hk
  have hk_le : k ≤ 3 := by omega
  interval_cases k
  · rfl
  · omega
  · exfalso
    have hb_eq : (R₂ \ R₁).card = 1 := by omega
    have hII := bipSum_self_le G (R₁ ∩ R₂)
    rw [← hk] at hII
    have hBB := bipSum_self_le G (R₂ \ R₁)
    rw [hb_eq] at hBB
    have hbip : 2 ≤ bipSum G (R₁ ∩ R₂) (R₂ \ R₁) := by omega
    exact not_two_adj_outside_of_leavingEndsDistinct hled1 Finset.inter_subset_left
      Finset.sdiff_disjoint hb_eq hbip
  · contradiction

lemma disjoint_crossedSquare_isolatedTriangle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {Q R : Finset (Fin n)}
    (hQ : Q ∈ crossedSquares G) (hR : R ∈ isolatedTriangles G) :
    Disjoint Q R := by
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
  obtain ⟨hcQ, hbQ⟩ := bipSum_of_mem_crossedSquares hQ
  obtain ⟨hcR, hbR, _, hledR, _⟩ := bipSum_of_mem_isolatedTriangles hR
  have ⟨hm, hXX, _⟩ := master_ineq G h3 Q R
  have hcs1 := Finset.card_inter_add_card_sdiff Q R
  have hcs2 := Finset.card_inter_add_card_sdiff R Q
  rw [Finset.inter_comm] at hcs2
  have hcardQ : (Q \ R).card = 4 - (Q ∩ R).card := by omega
  have hcardR : (R \ Q).card = 3 - (Q ∩ R).card := by omega
  rw [hbQ, hbR, hcardQ, hcardR] at hm
  rw [hbQ] at hXX
  set k := (Q ∩ R).card with hk
  have hk_le : k ≤ 3 := by omega
  interval_cases k
  · rfl
  · omega
  · omega
  · exfalso
    have ha_eq : (Q \ R).card = 1 := by omega
    have hII := bipSum_self_le G (Q ∩ R)
    rw [← hk] at hII
    have hAA := bipSum_self_le G (Q \ R)
    rw [ha_eq] at hAA
    have hbip : 2 ≤ bipSum G (Q ∩ R) (Q \ R) := by omega
    exact not_two_adj_outside_of_leavingEndsDistinct hledR Finset.inter_subset_right
      Finset.sdiff_disjoint ha_eq hbip

lemma disjoint_edgesWithin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {X Y : Finset (Fin n)} (h : Disjoint X Y) :
    Disjoint (edgesWithin G X) (edgesWithin G Y) := by
  rw [Finset.disjoint_left]
  intro e heX heY
  simp only [edgesWithin, Finset.mem_filter, Finset.mem_product] at heX heY
  exact Finset.disjoint_left.mp h heX.1.1 heY.1.1

lemma no_k4_of_connected_ne_four {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hconn : G.Connected) (hn4 : n ≠ 4)
    {Q : Finset (Fin n)} (hQcard : Q.card = 4) :
    (edgesWithin G Q).card ≤ 5 := by
  have hb_eq := bipSum_self_eq_two_mul_edgesWithin G Q
  have hb_le := bipSum_le_three_mul_card G h3 Q Q
  rw [hQcard] at hb_le
  by_contra hgt
  have h6 : (edgesWithin G Q).card = 6 := by omega
  have hb12 : bipSum G Q Q = 12 := by omega
  have hpart : bipSum G Q Q + bipSum G Q Qᶜ = 12 := by
    rw [← bipSum_union_right G Q disjoint_compl_right, Finset.union_compl,
      bipSum_univ_right G h3 Q, hQcard]
  have hcompl0 : bipSum G Q Qᶜ = 0 := by omega
  rw [bipSum, Finset.sum_eq_zero_iff] at hcompl0
  have hstep : ∀ {u v : Fin n}, u ∈ Q → G.Adj u v → v ∈ Q := by
    intro u v hu hadj
    by_contra hv
    have h0 := Finset.card_eq_zero.mp (hcompl0 u hu)
    have hmem : v ∈ Qᶜ.filter (G.Adj u) :=
      Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hv, hadj⟩
    rw [h0] at hmem
    exact Finset.notMem_empty v hmem
  have hwalk : ∀ {u v : Fin n} (w : G.Walk u v), u ∈ Q → v ∈ Q := by
    intro u v w
    induction w with
    | nil => exact id
    | cons hadj _ ih => intro hu; exact ih (hstep hu hadj)
  obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
  have huniv : Q = Finset.univ := by
    ext v
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨w⟩ := hconn u₀ v
    exact hwalk w hu₀
  have hncard : Q.card = n := by rw [huniv, Finset.card_univ, Fintype.card_fin]
  exact hn4 (hncard.symm.trans hQcard)

lemma commonNbrCount_le_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {j k : Fin n} (hjk : G.Adj j k) :
    commonNbrCount G j k ≤ 2 := by
  have hsub : (Finset.univ.filter fun u => G.Adj j u ∧ G.Adj k u) ⊆
      (Finset.univ.filter (G.Adj j)).erase k := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hu ⊢
    exact ⟨(G.ne_of_adj hu.2).symm, hu.1⟩
  have hk_mem : k ∈ Finset.univ.filter (G.Adj j) := by simp [hjk]
  calc commonNbrCount G j k
      ≤ ((Finset.univ.filter (G.Adj j)).erase k).card := Finset.card_le_card hsub
    _ = (Finset.univ.filter (G.Adj j)).card - 1 := Finset.card_erase_of_mem hk_mem
    _ = 2 := by rw [card_univ_filter_adj G h3 j]

lemma bipSum_erase_decomp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {X : Finset (Fin n)} {u : Fin n} (hu : u ∈ X) :
    bipSum G X X = 2 * (X.filter (G.Adj u)).card + bipSum G (X.erase u) (X.erase u) := by
  have hd : Disjoint {u} (X.erase u) := Finset.disjoint_singleton_left.mpr (Finset.notMem_erase u X)
  have hX : {u} ∪ X.erase u = X := by
    rw [Finset.singleton_union, Finset.insert_erase hu]
  have h1 := bipSum_union_self G hd
  rw [hX] at h1
  have h2 : bipSum G {u} (X.erase u) = (X.filter (G.Adj u)).card := by
    simp only [bipSum, Finset.sum_singleton]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun ⟨⟨_, hv⟩, hadj⟩ => ⟨hv, hadj⟩, fun ⟨hv, hadj⟩ => ⟨⟨(G.ne_of_adj hadj).symm, hv⟩, hadj⟩⟩
  rw [h1, bipSum_singleton_self, h2, zero_add]

lemma deg_in_crossedSquare {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Q : Finset (Fin n)} (hQ : Q ∈ crossedSquares G) {u : Fin n} (hu : u ∈ Q) :
    2 ≤ (Q.filter (G.Adj u)).card ∧ (Q.filter (G.Adj u)).card ≤ 3 := by
  obtain ⟨hc, hb⟩ := bipSum_of_mem_crossedSquares hQ
  have hdec := bipSum_erase_decomp G hu
  have her_card : (Q.erase u).card = 3 := by rw [Finset.card_erase_of_mem hu, hc]
  have her_le := bipSum_self_le G (Q.erase u)
  rw [her_card] at her_le
  have hsub : Q.filter (G.Adj u) ⊆ Q.erase u := by
    intro v hv
    rw [Finset.mem_filter] at hv
    exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hv.2).symm, hv.1⟩
  have hle3 : (Q.filter (G.Adj u)).card ≤ 3 := by
    rw [← her_card]
    exact Finset.card_le_card hsub
  omega

lemma bipSum_pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (hadj : G.Adj u v) :
    bipSum G {u, v} {u, v} = 2 := by
  have hne : u ≠ v := G.ne_of_adj hadj
  have hd : Disjoint {u} {v} := Finset.disjoint_singleton.mpr hne
  have hu : {u} ∪ {v} = ({u, v} : Finset (Fin n)) := rfl
  have h1 : bipSum G {u} {v} = 1 := by
    simp only [bipSum, Finset.sum_singleton]
    have heq : ({v} : Finset (Fin n)).filter (G.Adj u) = {v} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hadj⟩⟩
    rw [heq, Finset.card_singleton]
  rw [← hu, bipSum_union_self G hd, bipSum_singleton_self, bipSum_singleton_self, h1]

lemma edge_in_crossedSquare_props {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {Q : Finset (Fin n)} (hQ : Q ∈ crossedSquares G)
    {u v : Fin n} (hu : u ∈ Q) (hv : v ∈ Q) (hadj : G.Adj u v) :
    1 ≤ commonNbrCount G u v ∧ commonNbrCount G u v ≤ 2 ∧
      (commonNbrCount G u v = 2 ↔
        (Q.filter (G.Adj u)).card = 3 ∧ (Q.filter (G.Adj v)).card = 3) := by
  obtain ⟨hc, hb⟩ := bipSum_of_mem_crossedSquares hQ
  have hne : u ≠ v := G.ne_of_adj hadj
  let S := (Q.erase v).erase u
  have hv_er : u ∈ Q.erase v := Finset.mem_erase.mpr ⟨hne, hu⟩
  have hScard : S.card = 2 := by
    simp only [S]
    rw [Finset.card_erase_of_mem hv_er, Finset.card_erase_of_mem hv, hc]
  have hd : Disjoint {u, v} S := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [S, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase] at hx1 hx2
    rcases hx1 with rfl | rfl
    · exact hx2.1 rfl
    · exact hx2.2.1 rfl
  have hQS : {u, v} ∪ S = Q := by
    ext x
    by_cases hxu : x = u <;> by_cases hxv : x = v <;> simp [S, hxu, hxv, hu, hv]
  have hQ_decomp : bipSum G Q Q =
      bipSum G {u, v} {u, v} + 2 * bipSum G {u, v} S + bipSum G S S := by
    rw [← hQS, bipSum_union_self G hd]
  have huv_bip : bipSum G {u, v} S = (S.filter (G.Adj u)).card + (S.filter (G.Adj v)).card := by
    simp [bipSum, Finset.sum_pair hne]
  have hSS_le : bipSum G S S ≤ 2 := by
    have := bipSum_self_le G S
    rw [hScard] at this
    exact this
  have hpair := bipSum_pair_adj G hadj
  have hSu_deg : (Q.filter (G.Adj u)).card = (S.filter (G.Adj u)).card + 1 := by
    have heq : Q.filter (G.Adj u) = insert v (S.filter (G.Adj u)) := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hxQ, hux⟩
        by_cases hxv : x = v
        · exact Or.inl hxv
        · exact Or.inr ⟨⟨(G.ne_of_adj hux).symm, hxv, hxQ⟩, hux⟩
      · rintro (rfl | ⟨⟨_, _, hxQ⟩, hux⟩)
        · exact ⟨hv, hadj⟩
        · exact ⟨hxQ, hux⟩
    have hv_not : v ∉ S.filter (G.Adj u) := by
      simp [S]
    rw [heq, Finset.card_insert_of_notMem hv_not]
  have hSv_deg : (Q.filter (G.Adj v)).card = (S.filter (G.Adj v)).card + 1 := by
    have heq : Q.filter (G.Adj v) = insert u (S.filter (G.Adj v)) := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hxQ, hvx⟩
        by_cases hxu : x = u
        · exact Or.inl hxu
        · exact Or.inr ⟨⟨hxu, (G.ne_of_adj hvx).symm, hxQ⟩, hvx⟩
      · rintro (rfl | ⟨⟨_, _, hxQ⟩, hvx⟩)
        · exact ⟨hu, hadj.symm⟩
        · exact ⟨hxQ, hvx⟩
    have hu_not : u ∉ S.filter (G.Adj v) := by
      simp [S]
    rw [heq, Finset.card_insert_of_notMem hu_not]
  have hS_sum_ge : 3 ≤ (S.filter (G.Adj u)).card + (S.filter (G.Adj v)).card := by omega
  have hSu_le : (S.filter (G.Adj u)).card ≤ 2 := by
    rw [← hScard]; exact Finset.card_filter_le _ _
  have hSv_le : (S.filter (G.Adj v)).card ≤ 2 := by
    rw [← hScard]; exact Finset.card_filter_le _ _
  have h_no_out : ∀ w ∈ Qᶜ, ¬ (G.Adj u w ∧ G.Adj v w) := by
    rintro w hw ⟨huw, hvw⟩
    have h1 : 1 ≤ (Qᶜ.filter (G.Adj u)).card :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, huw⟩⟩
    have h2 : 1 ≤ (Qᶜ.filter (G.Adj v)).card :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hvw⟩⟩
    have h3u := card_filter_add_card_compl_filter G h3 Q u
    have h3v := card_filter_add_card_compl_filter G h3 Q v
    omega
  have hcn_eq : (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w) =
      S.filter (G.Adj u) ∩ S.filter (G.Adj v) := by
    ext w
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨huw, hvw⟩
      have hwQ : w ∈ Q := by
        by_contra hw
        exact h_no_out w (Finset.mem_compl.mpr hw) ⟨huw, hvw⟩
      exact ⟨⟨⟨(G.ne_of_adj huw).symm, (G.ne_of_adj hvw).symm, hwQ⟩, huw⟩,
        ⟨⟨(G.ne_of_adj huw).symm, (G.ne_of_adj hvw).symm, hwQ⟩, hvw⟩⟩
    · rintro ⟨⟨_, huw⟩, ⟨_, hvw⟩⟩
      exact ⟨huw, hvw⟩
  have hcn_card : commonNbrCount G u v = (S.filter (G.Adj u) ∩ S.filter (G.Adj v)).card := by
    rw [commonNbrCount, hcn_eq]
  have hunion_le : (S.filter (G.Adj u) ∪ S.filter (G.Adj v)).card ≤ 2 := by
    rw [← hScard]
    refine Finset.card_le_card ?_
    rw [Finset.union_subset_iff]
    exact ⟨Finset.filter_subset _ _, Finset.filter_subset _ _⟩
  have hiu := Finset.card_inter_add_card_union (S.filter (G.Adj u)) (S.filter (G.Adj v))
  have hinter_le_u : (S.filter (G.Adj u) ∩ S.filter (G.Adj v)).card ≤ (S.filter (G.Adj u)).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hinter_le_v : (S.filter (G.Adj u) ∩ S.filter (G.Adj v)).card ≤ (S.filter (G.Adj v)).card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

def E2In {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (Q : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (edgesWithin G Q).filter fun e => commonNbrCount G e.1 e.2 = 2

def E1In {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (Q : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (edgesWithin G Q).filter fun e => commonNbrCount G e.1 e.2 = 1

lemma card_E2In_and_E1In_of_mem_crossedSquares {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {Q : Finset (Fin n)} (hQ : Q ∈ crossedSquares G) :
    (E2In G Q).card = 1 ∧ (E1In G Q).card = 4 := by
  obtain ⟨hc, hb⟩ := bipSum_of_mem_crossedSquares hQ
  have hQ5 : (edgesWithin G Q).card = 5 := by
    simp only [crossedSquares, Finset.mem_filter] at hQ
    exact hQ.2
  let D := Q.filter fun u => (Q.filter (G.Adj u)).card = 3
  let B := Q.filter fun u => (Q.filter (G.Adj u)).card = 2
  have hdDB : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro u hD hB
    simp only [D, B, Finset.mem_filter] at hD hB
    omega
  have huDB : D ∪ B = Q := by
    ext u
    simp only [D, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
    · intro hu
      have := deg_in_crossedSquare hQ hu
      rcases (by omega : (Q.filter (G.Adj u)).card = 3 ∨ (Q.filter (G.Adj u)).card = 2) with h3c | h2c
      · exact Or.inl ⟨hu, h3c⟩
      · exact Or.inr ⟨hu, h2c⟩
  have hcardDB : D.card + B.card = 4 := by
    rw [← Finset.card_union_of_disjoint hdDB, huDB, hc]
  have hsumD : ∑ u ∈ D, (Q.filter (G.Adj u)).card = 3 * D.card := by
    have : ∀ u ∈ D, (Q.filter (G.Adj u)).card = 3 := by
      intro u hu; simp only [D, Finset.mem_filter] at hu; exact hu.2
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumB : ∑ u ∈ B, (Q.filter (G.Adj u)).card = 2 * B.card := by
    have : ∀ u ∈ B, (Q.filter (G.Adj u)).card = 2 := by
      intro u hu; simp only [B, Finset.mem_filter] at hu; exact hu.2
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumQ : 3 * D.card + 2 * B.card = 10 := by
    rw [← hsumD, ← hsumB, ← Finset.sum_union hdDB, huDB]
    exact hb
  have hDcard : D.card = 2 := by omega
  have hE2_eq : E2In G Q = (D ×ˢ D).filter fun e => e.1 < e.2 := by
    ext ⟨u, v⟩
    simp only [E2In, edgesWithin, D, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hu, hv⟩, hlt, hadj⟩, hcn⟩
      have hprops := (edge_in_crossedSquare_props h3 hQ hu hv hadj).2.2.mp hcn
      exact ⟨⟨⟨hu, hprops.1⟩, ⟨hv, hprops.2⟩⟩, hlt⟩
    · rintro ⟨⟨⟨hu, hdu⟩, ⟨hv, hdv⟩⟩, hlt⟩
      have hadj : G.Adj u v := by
        have hsub : Q.filter (G.Adj u) ⊆ Q.erase u := by
          intro x hx
          rw [Finset.mem_filter] at hx
          exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hx.2).symm, hx.1⟩
        have her_card : (Q.erase u).card = 3 := by rw [Finset.card_erase_of_mem hu, hc]
        have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
        have hv_mem : v ∈ Q.erase u := Finset.mem_erase.mpr ⟨hlt.ne', hv⟩
        rw [← heq, Finset.mem_filter] at hv_mem
        exact hv_mem.2
      have hcn := (edge_in_crossedSquare_props h3 hQ hu hv hadj).2.2.mpr ⟨hdu, hdv⟩
      exact ⟨⟨⟨hu, hv⟩, hlt, hadj⟩, hcn⟩
  have hE2_card : (E2In G Q).card = 1 := by
    rw [hE2_eq]
    obtain ⟨a, b, hab, hDab⟩ := Finset.card_eq_two.mp hDcard
    rw [hDab]
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have heq : ((({a, b} : Finset (Fin n)) ×ˢ ({a, b} : Finset (Fin n))).filter fun e => e.1 < e.2) =
          {(a, b)} := by
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro ⟨⟨rfl | rfl, rfl | rfl⟩, hxy⟩
          · exact (lt_irrefl _ hxy).elim
          · exact ⟨rfl, rfl⟩
          · exact (lt_asymm hlt hxy).elim
          · exact (lt_irrefl _ hxy).elim
        · rintro ⟨rfl, rfl⟩
          exact ⟨⟨Or.inl rfl, Or.inr rfl⟩, hlt⟩
      rw [heq, Finset.card_singleton]
    · have heq : ((({a, b} : Finset (Fin n)) ×ˢ ({a, b} : Finset (Fin n))).filter fun e => e.1 < e.2) =
          {(b, a)} := by
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro ⟨⟨rfl | rfl, rfl | rfl⟩, hxy⟩
          · exact (lt_irrefl _ hxy).elim
          · exact (lt_asymm hgt hxy).elim
          · exact ⟨rfl, rfl⟩
          · exact (lt_irrefl _ hxy).elim
        · rintro ⟨rfl, rfl⟩
          exact ⟨⟨Or.inr rfl, Or.inl rfl⟩, hgt⟩
      rw [heq, Finset.card_singleton]
  have hd21 : Disjoint (E2In G Q) (E1In G Q) := by
    rw [Finset.disjoint_left]
    intro e h2 h1
    simp only [E2In, E1In, Finset.mem_filter] at h2 h1
    omega
  have hu21 : E2In G Q ∪ E1In G Q = edgesWithin G Q := by
    ext e
    simp only [E2In, E1In, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      have he' := he
      simp only [edgesWithin, Finset.mem_filter, Finset.mem_product] at he'
      have ⟨h1, h2, _⟩ := edge_in_crossedSquare_props h3 hQ he'.1.1 he'.1.2 he'.2.2
      rcases (by omega : commonNbrCount G e.1 e.2 = 2 ∨ commonNbrCount G e.1 e.2 = 1) with h2c | h1c
      · exact Or.inl ⟨he, h2c⟩
      · exact Or.inr ⟨he, h1c⟩
  have hsum21 : (E2In G Q).card + (E1In G Q).card = 5 := by
    rw [← Finset.card_union_of_disjoint hd21, hu21, hQ5]
  exact ⟨hE2_card, by omega⟩

lemma commonNbrCount_eq_one_of_mem_isolatedTriangles {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {R : Finset (Fin n)} (hR : R ∈ isolatedTriangles G)
    {e : Fin n × Fin n} (he : e ∈ edgesWithin G R) :
    commonNbrCount G e.1 e.2 = 1 := by
  obtain ⟨hc, _, hclique, hled, _⟩ := bipSum_of_mem_isolatedTriangles hR
  simp only [edgesWithin, Finset.mem_filter, Finset.mem_product] at he
  rcases he with ⟨⟨hu, hv⟩, hlt, hadj⟩
  have heq : (Finset.univ.filter fun w => G.Adj e.1 w ∧ G.Adj e.2 w) = (R.erase e.2).erase e.1 := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨huw, hvw⟩
      have hwR : w ∈ R := by
        by_contra hw
        have hw' : w ∈ Rᶜ := Finset.mem_compl.mpr hw
        exact hled e.1 hu e.2 hv hlt.ne w hw' w hw' huw hvw rfl
      exact ⟨(G.ne_of_adj huw).symm, (G.ne_of_adj hvw).symm, hwR⟩
    · rintro ⟨hne1, hne2, hwR⟩
      exact ⟨hclique e.1 hu w hwR hne1.symm, hclique e.2 hv w hwR hne2.symm⟩
  have hu_er : e.1 ∈ R.erase e.2 := Finset.mem_erase.mpr ⟨hlt.ne, hu⟩
  rw [commonNbrCount, heq, Finset.card_erase_of_mem hu_er, Finset.card_erase_of_mem hv, hc]

lemma exists_crossedSquare_of_commonNbrCount_eq_two {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hconn : G.Connected) (hn4 : n ≠ 4)
    {u v : Fin n} (hlt : u < v) (hadj : G.Adj u v) (hcn : commonNbrCount G u v = 2) :
    ∃ Q ∈ crossedSquares G, (u, v) ∈ E2In G Q := by
  let C := Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w
  have hCcard : C.card = 2 := hcn
  have hd : Disjoint {u, v} C := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [C, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hx1 hx2
    rcases hx1 with rfl | rfl
    · exact G.ne_of_adj hx2.2.1 rfl
    · exact G.ne_of_adj hx2.2.2 rfl
  let Q := {u, v} ∪ C
  have hne : u ≠ v := hlt.ne
  have hQcard : Q.card = 4 := by
    rw [Finset.card_union_of_disjoint hd, Finset.card_pair hne, hCcard]
  have hbip_uv : bipSum G {u, v} {u, v} = 2 := bipSum_pair_adj G hadj
  have hCu : C.filter (G.Adj u) = C := by
    ext w; simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have hCv : C.filter (G.Adj v) = C := by
    ext w; simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have hbip_uvC : bipSum G {u, v} C = 4 := by
    simp only [bipSum, Finset.sum_pair hne, hCu, hCv, hCcard]
  have hQ_bip : 10 ≤ bipSum G Q Q := by
    dsimp only [Q]
    rw [bipSum_union_self G hd, hbip_uv, hbip_uvC]
    omega
  have hQ_edges_ge : 5 ≤ (edgesWithin G Q).card := by
    have := bipSum_self_eq_two_mul_edgesWithin G Q
    omega
  have hQ_edges_le := no_k4_of_connected_ne_four h3 hconn hn4 hQcard
  have hQ_edges : (edgesWithin G Q).card = 5 := by omega
  have hQ_mem : Q ∈ crossedSquares G := by
    simp only [crossedSquares, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ Q, hQcard⟩, hQ_edges⟩
  refine ⟨Q, hQ_mem, ?_⟩
  simp [E2In, edgesWithin, Q, hlt, hadj, hcn]

lemma exists_crossedSquare_or_isolatedTriangle_of_commonNbrCount_eq_one {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hconn : G.Connected) (hn4 : n ≠ 4)
    {u v : Fin n} (hlt : u < v) (hadj : G.Adj u v) (hcn : commonNbrCount G u v = 1) :
    (∃ Q ∈ crossedSquares G, (u, v) ∈ E1In G Q) ∨
      (∃ R ∈ isolatedTriangles G, (u, v) ∈ edgesWithin G R) := by
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcn
  have hw_mem : w ∈ Finset.univ.filter (fun z => G.Adj u z ∧ G.Adj v z) := by
    rw [hw]; exact Finset.mem_singleton_self w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw_mem
  rcases hw_mem with ⟨huw, hvw⟩
  have huv : u ≠ v := hlt.ne
  have huw_ne : u ≠ w := G.ne_of_adj huw
  have hvw_ne : v ≠ w := G.ne_of_adj hvw
  let R : Finset (Fin n) := {u, v, w}
  have hRcard : R.card = 3 := by
    have h1 : u ∉ ({v, w} : Finset (Fin n)) := by simp [huv, huw_ne]
    rw [Finset.card_insert_of_notMem h1, Finset.card_pair hvw_ne]
  have hRclique : SpansClique G R := by
    intro x hx y hy hxy
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact hadj
    · exact huw
    · exact hadj.symm
    · exact (hxy rfl).elim
    · exact hvw
    · exact huw.symm
    · exact hvw.symm
    · exact (hxy rfl).elim
  have heR : (u, v) ∈ edgesWithin G R := by
    simp [edgesWithin, R, hlt, hadj]
  by_cases hled : LeavingEndsDistinct G R
  · right
    refine ⟨R, ?_, heR⟩
    simp only [isolatedTriangles, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ R, hRcard⟩, hRclique, hled⟩
  · left
    simp only [LeavingEndsDistinct, not_forall] at hled
    obtain ⟨x, hx, y, hy, hxy, d₁, hd₁, d₂, hd₂, hxd₁, hyd₂, hd12⟩ := hled
    rw [not_ne_iff] at hd12
    subst hd12
    have hd_not : d₁ ∉ R := Finset.mem_compl.mp hd₁
    have hd_disj : Disjoint {d₁} R := Finset.disjoint_singleton_left.mpr hd_not
    let Q := {d₁} ∪ R
    have hQcard : Q.card = 4 := by
      rw [Finset.card_union_of_disjoint hd_disj, Finset.card_singleton, hRcard]
    have hRR := (bipSum_of_spansClique hRcard hRclique).1
    have hxy_sub : ({x, y} : Finset (Fin n)) ⊆ R.filter (G.Adj d₁) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [Finset.mem_filter]
      rcases hz with rfl | rfl
      · exact ⟨hx, hxd₁.symm⟩
      · exact ⟨hy, hyd₂.symm⟩
    have hdR_bip : 2 ≤ bipSum G {d₁} R := by
      simp only [bipSum, Finset.sum_singleton]
      rw [← Finset.card_pair hxy]
      exact Finset.card_le_card hxy_sub
    have hQ_bip : 10 ≤ bipSum G Q Q := by
      dsimp only [Q]
      rw [bipSum_union_self G hd_disj, hRR]
      omega
    have hQ_edges_ge : 5 ≤ (edgesWithin G Q).card := by
      have := bipSum_self_eq_two_mul_edgesWithin G Q
      omega
    have hQ_edges_le := no_k4_of_connected_ne_four h3 hconn hn4 hQcard
    have hQ_edges : (edgesWithin G Q).card = 5 := by omega
    have hQ_mem : Q ∈ crossedSquares G := by
      simp only [crossedSquares, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ Q, hQcard⟩, hQ_edges⟩
    refine ⟨Q, hQ_mem, ?_⟩
    simp [E1In, edgesWithin, Q, R, hlt, hadj, hcn]

end FarhiQAOA.Cubic.EdgeTypeCountAux

open QAlgorithms FarhiQAOA.Cubic FarhiQAOA.Cubic.EdgeTypeCountAux in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hconn : G.Connected) (hn4 : n ≠ 4) :
    ((Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n =>
        e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ commonNbrCount G e.1 e.2 = 2).card = S G ∧
      ((Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n =>
        e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ commonNbrCount G e.1 e.2 = 1).card = 4 * S G + 3 * T G := by
  let E2 := (Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n =>
    e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ commonNbrCount G e.1 e.2 = 2
  let E1 := (Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n =>
    e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ commonNbrCount G e.1 e.2 = 1
  have hE2_eq : E2 = (crossedSquares G).biUnion (E2In G) := by
    ext ⟨u, v⟩
    simp only [E2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    constructor
    · rintro ⟨hlt, hadj, hcn⟩
      exact exists_crossedSquare_of_commonNbrCount_eq_two h3 hconn hn4 hlt hadj hcn
    · rintro ⟨Q, _, he⟩
      simp only [E2In, edgesWithin, Finset.mem_filter, Finset.mem_product] at he
      exact ⟨he.1.2.1, he.1.2.2, he.2⟩
  have hE2_card : E2.card = S G := by
    rw [hE2_eq, Finset.card_biUnion]
    · have h1 : ∀ Q ∈ crossedSquares G, (E2In G Q).card = 1 :=
        fun Q hQ => (card_E2In_and_E1In_of_mem_crossedSquares h3 hQ).1
      rw [Finset.sum_congr rfl h1, Finset.sum_const, S, smul_eq_mul, mul_one]
    · intro Q₁ h1 Q₂ h2 hne
      exact (disjoint_edgesWithin G (disjoint_crossedSquares h3 h1 h2 hne)).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hE1_eq : E1 = (crossedSquares G).biUnion (E1In G) ∪
      (isolatedTriangles G).biUnion (edgesWithin G) := by
    ext ⟨u, v⟩
    simp only [E1, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro ⟨hlt, hadj, hcn⟩
      exact exists_crossedSquare_or_isolatedTriangle_of_commonNbrCount_eq_one h3 hconn hn4 hlt hadj hcn
    · rintro (⟨Q, _, he⟩ | ⟨R, hR, he⟩)
      · simp only [E1In, edgesWithin, Finset.mem_filter, Finset.mem_product] at he
        exact ⟨he.1.2.1, he.1.2.2, he.2⟩
      · have hcn := commonNbrCount_eq_one_of_mem_isolatedTriangles hR he
        simp only [edgesWithin, Finset.mem_filter, Finset.mem_product] at he
        exact ⟨he.2.1, he.2.2, hcn⟩
  have hd_QR : Disjoint ((crossedSquares G).biUnion (E1In G))
      ((isolatedTriangles G).biUnion (edgesWithin G)) := by
    rw [Finset.disjoint_biUnion_left]
    intro Q hQ
    rw [Finset.disjoint_biUnion_right]
    intro R hR
    exact (disjoint_edgesWithin G (disjoint_crossedSquare_isolatedTriangle h3 hQ hR)).mono_left
      (Finset.filter_subset _ _)
  have hE1_Q_card : ((crossedSquares G).biUnion (E1In G)).card = 4 * S G := by
    rw [Finset.card_biUnion]
    · have h4 : ∀ Q ∈ crossedSquares G, (E1In G Q).card = 4 :=
        fun Q hQ => (card_E2In_and_E1In_of_mem_crossedSquares h3 hQ).2
      rw [Finset.sum_congr rfl h4, Finset.sum_const, S, smul_eq_mul, mul_comm]
    · intro Q₁ h1 Q₂ h2 hne
      exact (disjoint_edgesWithin G (disjoint_crossedSquares h3 h1 h2 hne)).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hE1_R_card : ((isolatedTriangles G).biUnion (edgesWithin G)).card = 3 * T G := by
    rw [Finset.card_biUnion]
    · have h3c : ∀ R ∈ isolatedTriangles G, (edgesWithin G R).card = 3 :=
        fun R hR => (bipSum_of_mem_isolatedTriangles hR).2.2.2.2
      rw [Finset.sum_congr rfl h3c, Finset.sum_const, T, smul_eq_mul, mul_comm]
    · intro R₁ h1 R₂ h2 hne
      exact disjoint_edgesWithin G (disjoint_isolatedTriangles h3 h1 h2 hne)
  have hE1_card : E1.card = 4 * S G + 3 * T G := by
    rw [hE1_eq, Finset.card_union_of_disjoint hd_QR, hE1_Q_card, hE1_R_card]
  exact ⟨hE2_card, hE1_card⟩
