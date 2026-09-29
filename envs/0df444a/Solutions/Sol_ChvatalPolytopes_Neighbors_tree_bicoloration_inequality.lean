-- Prove2me | solution 1 for ChvatalPolytopes.Neighbors.tree_bicoloration_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:12:52.930721+00:00
-- url     : https://prove2.me/submissions/316876a3-dd7e-4798-aa45-8a0893aaa3f5

import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
import Definitions.Def_ChvatalPolytopes_Neighbors_IsBicoloration



namespace ChvatalPolytopes.Neighbors

open Classical in
lemma tb_inner_sum {V : Type*} [Fintype V] (T : SimpleGraph V) (x : V → ℝ) (u : V) :
    ∑ v, (if T.Adj u v then x u else 0) = (T.degree u : ℝ) * x u := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

open Classical in
lemma tb_double {V : Type*} [Fintype V] (T : SimpleGraph V) (x : V → ℝ) :
    ∑ u, ∑ v, (if T.Adj u v then x u + x v else 0) = 2 * ∑ u, (T.degree u : ℝ) * x u := by
  have h1 : ∀ u v, (if T.Adj u v then x u + x v else 0)
      = (if T.Adj u v then x u else 0) + (if T.Adj v u then x v else 0) := by
    intro u v
    by_cases h : T.Adj u v
    · simp [h, h.symm]
    · have h' : ¬ T.Adj v u := fun h'' => h h''.symm
      simp [h, h']
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun u v => if T.Adj v u then x v else 0)]
  simp_rw [tb_inner_sum]
  ring

open Classical in
lemma tb_ones {V : Type*} [Fintype V] (T : SimpleGraph V) :
    ∑ u, ∑ v, (if T.Adj u v then (1:ℝ) else 0) = 2 * (T.edgeFinset.card : ℝ) := by
  have := tb_double T (fun _ => (1/2 : ℝ))
  have h2 : ∀ u v, (if T.Adj u v then (1/2:ℝ) + 1/2 else 0) = if T.Adj u v then (1:ℝ) else 0 := by
    intro u v; norm_num
  simp only [h2] at this
  rw [this]
  have h3 := T.sum_degrees_eq_twice_card_edges
  have h4 : (∑ u, (T.degree u : ℝ)) = 2 * (T.edgeFinset.card : ℝ) := by exact_mod_cast h3
  rw [← Finset.sum_mul, h4]; ring

lemma tb_indicator_cases {V : Type*} [DecidableEq V] (S : Finset V) (u : V) :
    incidenceVector S u = 1 ∧ u ∈ S ∨ incidenceVector S u = 0 ∧ u ∉ S := by
  unfold incidenceVector; by_cases h : u ∈ S <;> simp [h]

lemma tb_walk {V : Type*} (T : SimpleGraph V) (P : V → Prop)
    (h : ∀ u v, T.Adj u v → (P u ↔ P v)) {a b : V} (p : T.Walk a b) : P a ↔ P b := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

theorem tb_core {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (B R : Finset V) (hBR : IsBicoloration T B R) :
    ∃ (c : V → ℕ) (m : ℕ), ∀ x ∈ stableVectors T,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) ↔ x = incidenceVector B ∨ x = incidenceVector R) := by
  classical
  refine ⟨fun u => T.degree u, T.edgeFinset.card, ?_⟩
  rintro x ⟨S, hS, rfl⟩
  set x := incidenceVector S with hx
  have hle : ∀ u v, (if T.Adj u v then x u + x v else 0) ≤ if T.Adj u v then (1:ℝ) else 0 := by
    intro u v
    by_cases h : T.Adj u v
    · simp only [h, if_true]
      rcases tb_indicator_cases S u with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;>
      rcases tb_indicator_cases S v with ⟨hv, hv'⟩ | ⟨hv, hv'⟩ <;> rw [hx, hu, hv] <;> try norm_num
      exact absurd h (hS hu' hv' (T.ne_of_adj h))
    · simp [h]
  have hsum : ∑ u, ∑ v, (if T.Adj u v then x u + x v else 0)
      ≤ ∑ u, ∑ v, (if T.Adj u v then (1:ℝ) else 0) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hle u v
  rw [tb_double, tb_ones] at hsum
  refine ⟨by linarith, ?_⟩
  -- equality characterization
  have heq : (∑ u, (T.degree u : ℝ) * x u = (T.edgeFinset.card : ℝ)) ↔
      ∀ u v, T.Adj u v → x u + x v = 1 := by
    constructor
    · intro hE u v huv
      have hE2 : ∑ u, ∑ v, (if T.Adj u v then x u + x v else 0)
          = ∑ u, ∑ v, (if T.Adj u v then (1:ℝ) else 0) := by
        rw [tb_double, tb_ones, hE]
      rw [Finset.sum_eq_sum_iff_of_le (fun u _ => Finset.sum_le_sum fun v _ => hle u v)] at hE2
      have := hE2 u (Finset.mem_univ _)
      rw [Finset.sum_eq_sum_iff_of_le (fun v _ => hle u v)] at this
      have := this v (Finset.mem_univ _)
      simpa [huv] using this
    · intro hall
      have hE2 : ∑ u, ∑ v, (if T.Adj u v then x u + x v else 0)
          = ∑ u, ∑ v, (if T.Adj u v then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        by_cases h : T.Adj u v
        · simp [h, hall u v h]
        · simp [h]
      rw [tb_double, tb_ones] at hE2
      linarith
  have hcast : (∑ u, (((fun u => T.degree u) u : ℕ) : ℝ) * x u) = ∑ u, (T.degree u : ℝ) * x u := rfl
  rw [hcast, heq]
  obtain ⟨hdisj, hunion, hadj⟩ := hBR
  have hR : ∀ u, u ∈ R ↔ u ∉ B := by
    intro u
    constructor
    · intro hu hb; exact Finset.disjoint_left.mp hdisj hb hu
    · intro hb
      have : u ∈ B ∪ R := by rw [hunion]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with h | h
      · exact absurd h hb
      · exact h
  have hxval : ∀ u, (x u = 1 ↔ u ∈ S) ∧ (x u = 0 ↔ u ∉ S) := by
    intro u
    rcases tb_indicator_cases S u with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;> rw [hx] <;> simp [hu, hu']
  constructor
  · intro hall
    -- P u := (u ∈ S ↔ u ∈ B)
    have hP : ∀ u v, T.Adj u v → ((u ∈ S ↔ u ∈ B) ↔ (v ∈ S ↔ v ∈ B)) := by
      intro u v huv
      have hs := hall u v huv
      have hb := hadj u v huv
      rw [hR, hR] at hb
      rcases tb_indicator_cases S u with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;>
      rcases tb_indicator_cases S v with ⟨hv, hv'⟩ | ⟨hv, hv'⟩ <;>
      rw [hx, hu, hv] at hs <;> norm_num at hs <;> tauto
    obtain ⟨v0⟩ := hT.1.nonempty
    have hall' : ∀ u, (u ∈ S ↔ u ∈ B) ↔ (v0 ∈ S ↔ v0 ∈ B) := by
      intro u
      obtain ⟨p⟩ := hT.1.preconnected u v0
      exact tb_walk T _ hP p
    by_cases h0 : (v0 ∈ S ↔ v0 ∈ B)
    · left
      have : S = B := by ext u; exact (hall' u).mpr h0
      rw [hx, this]
    · right
      have : S = R := by
        ext u; rw [hR]; have := (hall' u); tauto
      rw [hx, this]
  · rintro (h | h) u v huv
    · rw [h]; unfold incidenceVector
      have hb := hadj u v huv
      rw [hR, hR] at hb
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    · rw [h]; unfold incidenceVector
      have hb := hadj u v huv
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : u ∉ R := by rw [hR]; simpa using h1
        simp [this, h2]
      · have : v ∉ R := by rw [hR]; simpa using h2
        simp [this, h1]

end ChvatalPolytopes.Neighbors

open ChvatalPolytopes.Neighbors


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (B R : Finset V) (hBR : IsBicoloration T B R) :
    ∃ (c : V → ℕ) (m : ℕ), ∀ x ∈ stableVectors T,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) ↔ x = incidenceVector B ∨ x = incidenceVector R) := by
  exact tb_core T hT B R hBR
