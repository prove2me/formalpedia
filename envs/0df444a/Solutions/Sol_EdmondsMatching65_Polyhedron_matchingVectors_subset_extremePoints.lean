-- Prove2me | solution 1 for EdmondsMatching65.Polyhedron.matchingVectors_subset_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:23:47.300998+00:00
-- url     : https://prove2.me/submissions/51e49476-07b9-4a94-96a9-8e3a0fa2f668

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron

set_option autoImplicit false

namespace P600608b0
open EdmondsMatching65.Polyhedron

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma coord_le_one (G : EdmondsMatching65.Polyhedron.Graph V E) (y : E → ℝ) (hy : y ∈ matchingPolyhedron G) (e : E) :
    y e ≤ 1 := by
  obtain ⟨h0, h1, -⟩ := hy
  have hv : (G.ends e).out.1 ∈ G.ends e := Sym2.out_fst_mem _
  calc y e ≤ degSum G y (G.ends e).out.1 := by
        unfold degSum
        exact Finset.single_le_sum (f := y) (fun i _ => h0 i) (by simp [hv])
    _ ≤ 1 := h1 _

lemma two_insideSum_le (G : EdmondsMatching65.Polyhedron.Graph V E) (y : E → ℝ) (h0 : ∀ e, 0 ≤ y e) (S : Finset V) :
    2 * insideSum G y S ≤ ∑ v ∈ S, degSum G y v := by
  unfold insideSum degSum
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hl := G.loopless e
  have hy := h0 e
  generalize G.ends e = z at hl ⊢
  induction z using Sym2.ind with
  | h a b =>
    rw [Sym2.mk_isDiag_iff] at hl
    split_ifs with he
    · rw [Finset.mk_mem_sym2_iff] at he
      have hsub : ({a, b} : Finset V) ⊆ S := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact he.1
        · exact he.2
      calc 2 * y e = ∑ v ∈ ({a, b} : Finset V), (if v ∈ s(a, b) then y e else 0) := by
            rw [Finset.sum_pair hl]; simp; ring
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => by
            split_ifs <;> linarith)
    · simp only [mul_zero]
      exact Finset.sum_nonneg (fun v _ => by split_ifs <;> linarith)

end P600608b0

open EdmondsMatching65.Polyhedron in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) :
    matchingVectors G ⊆ Set.extremePoints ℝ (matchingPolyhedron G) := by
  intro x hx
  obtain ⟨h01, hdeg⟩ := hx
  have h0 : ∀ e, 0 ≤ x e := fun e => by rcases h01 e with h | h <;> simp [h]
  have hmem : x ∈ matchingPolyhedron G := by
    refine ⟨h0, hdeg, ?_⟩
    intro S r _ hS
    obtain ⟨k, hk⟩ : ∃ k : ℕ, insideSum G x S = k := by
      refine ⟨∑ e ∈ Finset.univ.filter (fun e => G.ends e ∈ S.sym2),
        if x e = 1 then 1 else 0, ?_⟩
      unfold insideSum
      push_cast
      apply Finset.sum_congr rfl
      intro e _
      rcases h01 e with h | h <;> simp [h]
    have h2 := P600608b0.two_insideSum_le G x h0 S
    have h3 : ∑ v ∈ S, degSum G x v ≤ ((2 * r + 1 : ℕ) : ℝ) := by
      calc _ ≤ ∑ v ∈ S, (1 : ℝ) := Finset.sum_le_sum fun v _ => hdeg v
        _ = _ := by simp [hS]
    rw [hk] at h2 ⊢
    have h4 : 2 * k ≤ 2 * r + 1 := by exact_mod_cast h2.trans h3
    exact_mod_cast (by omega : k ≤ r)
  rw [mem_extremePoints]
  refine ⟨hmem, fun x1 hx1 x2 hx2 hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have c1 := P600608b0.coord_le_one G x1 hx1
  have c2 := P600608b0.coord_le_one G x2 hx2
  have n1 := hx1.1
  have n2 := hx2.1
  have key : ∀ e, x1 e = (a • x1 + b • x2) e ∧ x2 e = (a • x1 + b • x2) e := by
    intro e
    have he := h01 e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he ⊢
    have u1 := c1 e
    have u2 := c2 e
    have v1 := n1 e
    have v2 := n2 e
    have w1 := mul_nonneg ha.le v1
    have w2 := mul_nonneg hb.le v2
    have w3 := mul_nonneg ha.le (sub_nonneg.2 u1)
    have w4 := mul_nonneg hb.le (sub_nonneg.2 u2)
    rcases he with h | h
    · have p1 : a * x1 e = 0 := by linarith
      have p2 : b * x2 e = 0 := by linarith
      have q1 : x1 e = 0 := by
        rcases mul_eq_zero.1 p1 with h' | h'
        · exact absurd h' ha.ne'
        · exact h'
      have q2 : x2 e = 0 := by
        rcases mul_eq_zero.1 p2 with h' | h'
        · exact absurd h' hb.ne'
        · exact h'
      rw [h]; exact ⟨q1, q2⟩
    · have p1 : a * (1 - x1 e) = 0 := by nlinarith
      have p2 : b * (1 - x2 e) = 0 := by nlinarith
      have q1 : x1 e = 1 := by
        rcases mul_eq_zero.1 p1 with h' | h'
        · exact absurd h' ha.ne'
        · linarith
      have q2 : x2 e = 1 := by
        rcases mul_eq_zero.1 p2 with h' | h'
        · exact absurd h' hb.ne'
        · linarith
      rw [h]; exact ⟨q1, q2⟩
  exact ⟨funext fun e => (key e).1, funext fun e => (key e).2⟩
