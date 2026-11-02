-- Prove2me | solution 1 for FarhiQAOA.Cubic.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:47:14.538672+00:00
-- url     : https://prove2.me/submissions/bdbf8485-6026-4014-a1cd-2884eeb354e2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types
import Theorems.Thm_FarhiQAOA_Cubic_edge_term_subgraph_type
import Theorems.Thm_FarhiQAOA_Cubic_edge_type_count

namespace FarhiQAOA.Cubic.Eq32Aux

open QAlgorithms FarhiQAOA.Cubic

lemma F1_eq_sum_edgesWithin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (γ β : ℝ) :
    F1 G γ β = ∑ e ∈ edgesWithin G Finset.univ, edgeTerm1 G γ β e.1 e.2 := by
  simp only [F1, expectCut, cutValue, edgeTerm1, edgeTerm, edgesWithin, Finset.sum_filter,
    Finset.sum_product]
  trans ∑ z : Qubits n, ∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ G.Adj u v then prob (qaoaState G 1 (fun _ => γ) (fun _ => β)) z * edgeCut u v z else 0
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · rfl
    · simp

lemma commonNbrCount_le_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) {j k : Fin n} (hjk : G.Adj j k) :
    commonNbrCount G j k ≤ 2 := by
  have hsub : (Finset.univ.filter fun u => G.Adj j u ∧ G.Adj k u) ⊆
      (Finset.univ.filter (G.Adj j)).erase k := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hu ⊢
    exact ⟨(G.ne_of_adj hu.2).symm, hu.1⟩
  have hk_mem : k ∈ Finset.univ.filter (G.Adj j) := by simp [hjk]
  have hdeg : (Finset.univ.filter (G.Adj j)).card = 3 := by
    have heq : Finset.univ.filter (G.Adj j) = G.neighborFinset j := by
      ext v; simp [SimpleGraph.mem_neighborFinset]
    rw [heq, SimpleGraph.card_neighborFinset_eq_degree, h3 j]
  calc commonNbrCount G j k
      ≤ ((Finset.univ.filter (G.Adj j)).erase k).card := Finset.card_le_card hsub
    _ = (Finset.univ.filter (G.Adj j)).card - 1 := Finset.card_erase_of_mem hk_mem
    _ = 2 := by rw [hdeg]

lemma two_mul_card_edgesWithin_univ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) :
    2 * (edgesWithin G Finset.univ).card = 3 * n := by
  have h1 : ∑ u : Fin n, (Finset.univ.filter (G.Adj u)).card =
      ((Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n => G.Adj e.1 e.2).card := by
    simp only [Finset.card_filter, Finset.sum_product]
  have h2 : ∑ u : Fin n, (Finset.univ.filter (G.Adj u)).card = 3 * n := by
    have hcard : ∀ u ∈ (Finset.univ : Finset (Fin n)), (Finset.univ.filter (G.Adj u)).card = 3 := by
      intro u _
      have heq : Finset.univ.filter (G.Adj u) = G.neighborFinset u := by
        ext v; simp [SimpleGraph.mem_neighborFinset]
      rw [heq, SimpleGraph.card_neighborFinset_eq_degree, h3 u]
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_comm]
  let s1 := (Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n => e.1 < e.2 ∧ G.Adj e.1 e.2
  let s2 := (Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n => e.2 < e.1 ∧ G.Adj e.1 e.2
  have hsplit : ((Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n => G.Adj e.1 e.2) = s1 ∪ s2 := by
    ext ⟨u, v⟩
    simp only [s1, s2, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · intro hadj
      rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
      · exact Or.inl ⟨hlt, hadj⟩
      · exact Or.inr ⟨hgt, hadj⟩
    · rintro (⟨_, hadj⟩ | ⟨_, hadj⟩) <;> exact hadj
  have hdisj : Disjoint s1 s2 := by
    rw [Finset.disjoint_left]
    intro ⟨u, v⟩ ha hb
    simp only [s1, s2, Finset.mem_filter] at ha hb
    exact lt_asymm ha.2.1 hb.2.1
  have hswap : s2.card = s1.card := by
    refine Finset.card_bij (fun e _ => Prod.swap e) ?_ ?_ ?_
    · intro ⟨u, v⟩ h
      simp only [s1, s2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Prod.swap] at h ⊢
      exact ⟨h.1, h.2.symm⟩
    · intro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h
      exact Prod.swap_injective h
    · intro ⟨u, v⟩ h
      refine ⟨(v, u), ?_, rfl⟩
      simp only [s1, s2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at h ⊢
      exact ⟨h.1, h.2.symm⟩
  have h3_eq : ((Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n => G.Adj e.1 e.2).card =
      2 * (edgesWithin G Finset.univ).card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj, hswap, two_mul]
    rfl
  omega

end FarhiQAOA.Cubic.Eq32Aux

open QAlgorithms FarhiQAOA.Cubic FarhiQAOA.Cubic.Eq32Aux in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hconn : G.Connected) (hn4 : n ≠ 4) (γ β : ℝ) :
    F1 G γ β = (S G : ℝ) * fg4 γ β + (4 * (S G : ℝ) + 3 * (T G : ℝ)) * fg5 γ β +
      ((3 : ℝ) / 2 * (n : ℝ) - 5 * (S G : ℝ) - 3 * (T G : ℝ)) * fg6 γ β := by
  rw [F1_eq_sum_edgesWithin]
  let E := edgesWithin G Finset.univ
  let E2 := E.filter fun e => commonNbrCount G e.1 e.2 = 2
  let E1 := E.filter fun e => commonNbrCount G e.1 e.2 = 1
  let E0 := E.filter fun e => commonNbrCount G e.1 e.2 = 0
  have hterm : ∀ e ∈ E, edgeTerm1 G γ β e.1 e.2 =
      (if commonNbrCount G e.1 e.2 = 2 then fg4 γ β else 0) +
      (if commonNbrCount G e.1 e.2 = 1 then fg5 γ β else 0) +
      (if commonNbrCount G e.1 e.2 = 0 then fg6 γ β else 0) := by
    intro e he
    have hadj : G.Adj e.1 e.2 := by
      simp only [E, edgesWithin, Finset.mem_filter] at he
      exact he.2.2
    have hle2 := commonNbrCount_le_two G h3 hadj
    obtain ⟨h4, h5, h6⟩ := edge_term_subgraph_type G h3 e.1 e.2 hadj γ β
    set c := commonNbrCount G e.1 e.2
    interval_cases c
    · simp [h6 rfl]
    · simp [h5 rfl]
    · simp [h4 rfl]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsum2 : (∑ e ∈ E, if commonNbrCount G e.1 e.2 = 2 then fg4 γ β else 0) =
      (E2.card : ℝ) * fg4 γ β := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hsum1 : (∑ e ∈ E, if commonNbrCount G e.1 e.2 = 1 then fg5 γ β else 0) =
      (E1.card : ℝ) * fg5 γ β := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hsum0 : (∑ e ∈ E, if commonNbrCount G e.1 e.2 = 0 then fg6 γ β else 0) =
      (E0.card : ℝ) * fg6 γ β := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hsum2, hsum1, hsum0]
  have hcount := edge_type_count G h3 hconn hn4
  have hE2_eq : E2 = (Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n =>
      e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ commonNbrCount G e.1 e.2 = 2 := by
    ext e
    simp only [E2, E, edgesWithin, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    tauto
  have hE1_eq : E1 = (Finset.univ ×ˢ Finset.univ).filter fun e : Fin n × Fin n =>
      e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ commonNbrCount G e.1 e.2 = 1 := by
    ext e
    simp only [E1, E, edgesWithin, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    tauto
  have hE2_card : E2.card = S G := by rw [hE2_eq, hcount.1]
  have hE1_card : E1.card = 4 * S G + 3 * T G := by rw [hE1_eq, hcount.2]
  have hpart : E2 ∪ E1 ∪ E0 = E := by
    ext e
    simp only [E2, E1, E0, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((⟨he, _⟩ | ⟨he, _⟩) | ⟨he, _⟩) <;> exact he
    · intro he
      have hadj : G.Adj e.1 e.2 := by
        simp only [E, edgesWithin, Finset.mem_filter] at he
        exact he.2.2
      have hle2 := commonNbrCount_le_two G h3 hadj
      set c := commonNbrCount G e.1 e.2
      interval_cases c <;> simp [he]
  have hd21 : Disjoint E2 E1 := by
    rw [Finset.disjoint_left]
    intro e h2 h1
    simp only [E2, E1, Finset.mem_filter] at h2 h1
    omega
  have hd21_0 : Disjoint (E2 ∪ E1) E0 := by
    rw [Finset.disjoint_left]
    intro e h21 h0
    simp only [E2, E1, E0, Finset.mem_union, Finset.mem_filter] at h21 h0
    rcases h21 with ⟨_, hc⟩ | ⟨_, hc⟩ <;> omega
  have hcard_sum : E2.card + E1.card + E0.card = E.card := by
    rw [← Finset.card_union_of_disjoint hd21, ← Finset.card_union_of_disjoint hd21_0, hpart]
  have h2m := two_mul_card_edgesWithin_univ G h3
  have hcard_real : (E2.card : ℝ) + (E1.card : ℝ) + (E0.card : ℝ) = (E.card : ℝ) := by
    exact_mod_cast hcard_sum
  have h2m_real : 2 * (E.card : ℝ) = 3 * (n : ℝ) := by
    exact_mod_cast h2m
  have hE2_real : (E2.card : ℝ) = (S G : ℝ) := by exact_mod_cast hE2_card
  have hE1_real : (E1.card : ℝ) = 4 * (S G : ℝ) + 3 * (T G : ℝ) := by exact_mod_cast hE1_card
  have hE0_real : (E0.card : ℝ) = (3 : ℝ) / 2 * (n : ℝ) - 5 * (S G : ℝ) - 3 * (T G : ℝ) := by
    linarith
  rw [hE2_real, hE1_real, hE0_real]
