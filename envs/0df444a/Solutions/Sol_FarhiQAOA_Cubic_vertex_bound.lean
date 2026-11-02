-- Prove2me | solution 1 for FarhiQAOA.Cubic.vertex_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:44:25.152681+00:00
-- url     : https://prove2.me/submissions/a6bb96bd-d9ac-463d-a3c9-68685e712946

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic.VertexBoundAux

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

lemma bipSum_le_three_mul_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (X Y : Finset (Fin n)) :
    bipSum G X Y ≤ 3 * X.card := by
  have hle : ∀ u ∈ X, (Y.filter (G.Adj u)).card ≤ 3 := by
    intro u _
    have hdeg : Finset.univ.filter (G.Adj u) = G.neighborFinset u := by
      ext v; simp [SimpleGraph.mem_neighborFinset]
    calc (Y.filter (G.Adj u)).card
        ≤ (Finset.univ.filter (G.Adj u)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ Y))
      _ = G.degree u := by rw [hdeg, SimpleGraph.card_neighborFinset_eq_degree]
      _ = 3 := h3 u
  calc bipSum G X Y ≤ ∑ _u ∈ X, 3 := Finset.sum_le_sum hle
    _ = 3 * X.card := by simp [mul_comm]

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

lemma bipSum_of_mem_isolatedTriangles {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {R : Finset (Fin n)} (hR : R ∈ isolatedTriangles G) :
    R.card = 3 ∧ bipSum G R R = 6 ∧ SpansClique G R ∧ LeavingEndsDistinct G R := by
  simp only [isolatedTriangles, Finset.mem_filter, Finset.mem_powersetCard] at hR
  refine ⟨hR.1.2, ?_, hR.2.1, hR.2.2⟩
  have hcard : ∀ u ∈ R, (R.filter (G.Adj u)).card = 2 := by
    intro u hu
    have heq : R.filter (G.Adj u) = R.erase u := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hv, hadj⟩
        exact ⟨(G.ne_of_adj hadj).symm, hv⟩
      · rintro ⟨hne, hv⟩
        exact ⟨hv, hR.2.1 u hu v hv hne.symm⟩
    rw [heq, Finset.card_erase_of_mem hu, hR.1.2]
  simp only [bipSum]
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, hR.1.2]
  rfl

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
  obtain ⟨hc1, hb1, _, hled1⟩ := bipSum_of_mem_isolatedTriangles h1
  obtain ⟨hc2, hb2, _, _⟩ := bipSum_of_mem_isolatedTriangles h2
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
  obtain ⟨hcR, hbR, _, hledR⟩ := bipSum_of_mem_isolatedTriangles hR
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

end FarhiQAOA.Cubic.VertexBoundAux

open QAlgorithms FarhiQAOA.Cubic FarhiQAOA.Cubic.VertexBoundAux in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) :
    3 * T G + 4 * S G ≤ n := by
  let U₁ := (isolatedTriangles G).biUnion id
  let U₂ := (crossedSquares G).biUnion id
  have hU₁ : U₁.card = 3 * T G := by
    dsimp only [U₁]
    rw [Finset.card_biUnion]
    · have hcard : ∀ R ∈ isolatedTriangles G, (id R).card = 3 :=
        fun R hR => (bipSum_of_mem_isolatedTriangles hR).1
      rw [Finset.sum_congr rfl hcard, Finset.sum_const, T, smul_eq_mul, mul_comm]
    · intro R₁ h1 R₂ h2 hne
      exact disjoint_isolatedTriangles h3 h1 h2 hne
  have hU₂ : U₂.card = 4 * S G := by
    dsimp only [U₂]
    rw [Finset.card_biUnion]
    · have hcard : ∀ Q ∈ crossedSquares G, (id Q).card = 4 :=
        fun Q hQ => (bipSum_of_mem_crossedSquares hQ).1
      rw [Finset.sum_congr rfl hcard, Finset.sum_const, S, smul_eq_mul, mul_comm]
    · intro Q₁ h1 Q₂ h2 hne
      exact disjoint_crossedSquares h3 h1 h2 hne
  have hd : Disjoint U₁ U₂ := by
    dsimp only [U₁, U₂]
    rw [Finset.disjoint_biUnion_left]
    intro R hR
    rw [Finset.disjoint_biUnion_right]
    intro Q hQ
    exact (disjoint_crossedSquare_isolatedTriangle h3 hQ hR).symm
  calc 3 * T G + 4 * S G
      = U₁.card + U₂.card := by rw [hU₁, hU₂]
    _ = (U₁ ∪ U₂).card := (Finset.card_union_of_disjoint hd).symm
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp
