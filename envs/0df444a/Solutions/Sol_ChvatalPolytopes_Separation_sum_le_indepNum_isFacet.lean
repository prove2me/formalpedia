-- Prove2me | solution 1 for ChvatalPolytopes.Separation.sum_le_indepNum_isFacet
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:33:51.540142+00:00
-- url     : https://prove2.me/submissions/9f4e50b0-fe6a-4a13-97f9-21b3572301bb

import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Separation_IsFacet
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical



namespace ChvatalPolytopes.Separation

open Filter Topology

lemma fct_incid_sum {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ) (S : Finset V) :
    ∑ u, f u * Shared.incidenceVector S u = ∑ u ∈ S, f u := by
  simp only [Shared.incidenceVector, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma fct_edge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (a : V → ℝ) (β : ℝ)
    (ha : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card = G.indepNum → ∑ u ∈ S, a u = β)
    {p q : V} (hpq : (criticalGraph G).Adj p q) : a p = a q := by
  rw [criticalGraph, SimpleGraph.fromEdgeSet_adj] at hpq
  obtain ⟨⟨hE, h2⟩, hne⟩ := hpq
  obtain ⟨T, hT⟩ := (G.deleteEdges {s(p, q)}).exists_isNIndepSet_indepNum
  have hprop : ∀ a ∈ T, ∀ b ∈ T, G.Adj a b → (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
    intro a ha b hb hab
    by_contra hne'
    have hab' : (G.deleteEdges {s(p, q)}).Adj a b := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hab, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      tauto
    exact hT.isIndepSet (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hab.ne hab'
  have hcard : T.card = G.indepNum + 1 := by rw [hT.card_eq, h2]
  have hpT : p ∈ T ∧ q ∈ T := by
    by_contra hpq
    have hind : G.IsIndepSet (T : Set V) := by
      intro a ha b hb _ hab
      rcases hprop a ha b hb hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpq ⟨ha, hb⟩
      · exact hpq ⟨hb, ha⟩
    have := hind.card_le_indepNum
    omega
  have hind_erase : ∀ r, (r = p ∨ r = q) → G.IsIndepSet ((T.erase r : Finset V) : Set V) := by
    intro r hr a ha b hb _ hab
    have ha' : a ∈ T.erase r := ha
    have hb' : b ∈ T.erase r := hb
    rw [Finset.mem_erase] at ha' hb'
    rcases hprop a ha'.2 b hb'.2 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hr with rfl | rfl <;>
      tauto
  have e1 := ha _ (hind_erase p (Or.inl rfl)) (by rw [Finset.card_erase_of_mem hpT.1]; omega)
  have e2 := ha _ (hind_erase q (Or.inr rfl)) (by rw [Finset.card_erase_of_mem hpT.2]; omega)
  have s1 := Finset.sum_erase_add T a hpT.1
  have s2 := Finset.sum_erase_add T a hpT.2
  linarith

lemma fct_const {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : (criticalGraph G).Connected) (a : V → ℝ) (β : ℝ)
    (ha : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card = G.indepNum → ∑ u ∈ S, a u = β)
    (u v : V) : a u = a v := by
  obtain ⟨p⟩ := hconn.preconnected u v
  induction p with
  | nil => rfl
  | cons h _ ih => exact (fct_edge G a β ha h).trans ih

theorem fct_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : (criticalGraph G).Connected) :
    IsFacet (Shared.stablePolytope G) (fun _ => 1) (G.indepNum : ℝ) := by
  classical
  intro J _ A B hsys
  haveI : Nonempty V := hconn.nonempty
  set α := G.indepNum with hα
  -- validity of the stable vectors
  have hvalid : ∀ S : Finset V, G.IsIndepSet (S : Set V) → ∀ j, ∑ u ∈ S, A j u ≤ B j := by
    intro S hS j
    have hmem : Shared.incidenceVector S ∈ Shared.stablePolytope G :=
      subset_convexHull ℝ _ ⟨S, hS, rfl⟩
    rw [← hsys] at hmem
    have := hmem j
    rwa [fct_incid_sum] at this
  -- P ⊆ {Σ x ≤ α}
  have hP : ∀ x ∈ Shared.stablePolytope G, ∑ u, x u ≤ (α : ℝ) := by
    intro x hx
    unfold Shared.stablePolytope at hx
    suffices hsub : convexHull ℝ (Shared.stableVectors G) ⊆ {x : V → ℝ | ∑ u, x u ≤ (α : ℝ)} from
      hsub hx
    apply convexHull_min
    · rintro _ ⟨S, hS, rfl⟩
      show ∑ u, Shared.incidenceVector S u ≤ (α : ℝ)
      have := fct_incid_sum (fun _ => (1 : ℝ)) S
      simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at this
      rw [this]
      exact_mod_cast hS.card_le_indepNum
    · intro y hy z hz s t hs ht hst
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum] at hy hz ⊢
      have := mul_le_mul_of_nonneg_left hy hs
      have := mul_le_mul_of_nonneg_left hz ht
      have : (α : ℝ) = s * α + t * α := by rw [← add_mul, hst, one_mul]
      linarith
  -- maximum stable sets
  set M := Finset.univ.filter (fun S : Finset V => G.IsIndepSet (S : Set V) ∧ S.card = α) with hM
  have hMne : M.Nonempty := by
    obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
    exact ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ _, hS.isIndepSet, hS.card_eq⟩⟩
  have hMpos : (0 : ℝ) < M.card := by exact_mod_cast hMne.card_pos
  set z : V → ℝ := fun u => (1 / (M.card : ℝ)) * ∑ S ∈ M, Shared.incidenceVector S u with hz
  have hzf : ∀ f : V → ℝ, ∑ u, f u * z u = (1 / (M.card : ℝ)) * ∑ S ∈ M, ∑ u ∈ S, f u := by
    intro f
    calc ∑ u, f u * z u = ∑ u, ∑ S ∈ M, (1 / (M.card : ℝ)) * (f u * Shared.incidenceVector S u) := by
          apply Finset.sum_congr rfl; intro u _
          simp only [hz]
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro S _; ring
      _ = ∑ S ∈ M, ∑ u, (1 / (M.card : ℝ)) * (f u * Shared.incidenceVector S u) := Finset.sum_comm
      _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro S _
          rw [← fct_incid_sum f S, Finset.mul_sum]
  have hzrow : ∀ j, ∑ u, A j u * z u = (1 / (M.card : ℝ)) * ∑ S ∈ M, ∑ u ∈ S, A j u :=
    fun j => hzf (A j)
  have hzsum : ∑ u, z u = (α : ℝ) := by
    have h1 := hzf (fun _ => 1)
    simp only [one_mul] at h1
    rw [h1]
    have h2 : ∑ S ∈ M, ∑ u ∈ S, (1 : ℝ) = ∑ S ∈ M, (α : ℝ) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.mem_filter] at hS
      simp [hS.2.2]
    rw [h2, Finset.sum_const, nsmul_eq_mul]
    field_simp
  -- tight rows at z are tight at all maximum stable sets
  have htight : ∀ j, ∑ u, A j u * z u = B j → ∃ t : ℝ, (∀ u, A j u = t * 1) ∧ B j = t * α := by
    intro j hj
    rw [hzrow] at hj
    have hall : ∀ S ∈ M, ∑ u ∈ S, A j u = B j := by
      have hsum0 : ∑ S ∈ M, (B j - ∑ u ∈ S, A j u) = 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        field_simp at hj
        linarith
      rw [Finset.sum_eq_zero_iff_of_nonneg] at hsum0
      · intro S hS; linarith [hsum0 S hS]
      · intro S hS
        rw [Finset.mem_filter] at hS
        linarith [hvalid S hS.2.1 j]
    have hconst := fct_const G hconn (A j) (B j)
      (fun S hS hc => hall S (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS, hc⟩))
    let u0 := Classical.arbitrary V
    refine ⟨A j u0, fun u => by rw [mul_one]; exact hconst u u0, ?_⟩
    obtain ⟨S, hS⟩ := hMne
    have := hall S hS
    rw [Finset.mem_filter] at hS
    rw [← this, Finset.sum_congr rfl (fun u _ => hconst u u0), Finset.sum_const, hS.2.2,
      nsmul_eq_mul, mul_comm]
  by_contra hno
  push_neg at hno
  -- find ε > 0 with z + ε ∈ P
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ j, ∑ u, A j u * z u < B j →
      ∑ u, A j u * (z u + ε) < B j := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : ∑ u, A j u * z u < B j
    · have hc : ContinuousAt (fun ε : ℝ => ∑ u, A j u * (z u + ε)) 0 := by fun_prop
      have := hc.eventually_lt continuousAt_const (by simpa using hj)
      filter_upwards [this] with ε hε _ using hε
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hj)
  obtain ⟨ε, hε, hεpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hmem : (fun u => z u + ε) ∈ Shared.stablePolytope G := by
    rw [← hsys]
    intro j
    have hzj : ∑ u, A j u * z u ≤ B j := by
      rw [hzrow]
      have : ∑ S ∈ M, ∑ u ∈ S, A j u ≤ ∑ S ∈ M, B j := by
        apply Finset.sum_le_sum
        intro S hS
        rw [Finset.mem_filter] at hS
        exact hvalid S hS.2.1 j
      rw [Finset.sum_const, nsmul_eq_mul] at this
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hMpos]
      linarith
    rcases hzj.lt_or_eq with hlt | heq
    · exact (hε j hlt).le
    · obtain ⟨t, ht1, ht2⟩ := htight j heq
      have htle : t ≤ 0 := by
        by_contra htpos
        push_neg at htpos
        exact absurd ht2 (hno j t htpos ht1)
      have : ∑ u, A j u * (z u + ε) = ∑ u, A j u * z u + t * ε * Fintype.card V := by
        simp only [mul_add, Finset.sum_add_distrib, ht1, mul_one, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        ring
      rw [this, heq]
      have : t * ε * (Fintype.card V : ℝ) ≤ 0 := by
        have : (0 : ℝ) ≤ ε * Fintype.card V := by positivity
        nlinarith
      linarith
  have h1 := hP _ hmem
  have h2 : ∑ u, (z u + ε) = α + ε * Fintype.card V := by
    rw [Finset.sum_add_distrib, hzsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  have hcardpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have : 0 < ε * (Fintype.card V : ℝ) := mul_pos hεpos hcardpos
  linarith

end ChvatalPolytopes.Separation

open ChvatalPolytopes.Separation
open ChvatalPolytopes ChvatalPolytopes.Separation

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : (criticalGraph G).Connected) :
    IsFacet (Shared.stablePolytope G) (fun _ => 1) (G.indepNum : ℝ) := by
  exact fct_core G hconn
