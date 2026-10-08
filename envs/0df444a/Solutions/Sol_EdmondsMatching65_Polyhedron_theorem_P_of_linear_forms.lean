-- Prove2me | solution 1 for EdmondsMatching65.Polyhedron.theorem_P_of_linear_forms
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:48:07.948063+00:00
-- url     : https://prove2.me/submissions/b6e08feb-05cf-4d64-a3a0-fd317dac902d

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron



namespace EdmondsMatching65.Polyhedron

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma plf_le_one (G : Graph V E) (x : E → ℝ) (hx : x ∈ matchingPolyhedron G) (e : E) :
    x e ≤ 1 := by
  obtain ⟨h0, hd, -⟩ := hx
  have hu : (G.ends e).out.1 ∈ G.ends e := Sym2.out_fst_mem _
  calc x e ≤ degSum G x (G.ends e).out.1 := by
        unfold degSum
        exact Finset.single_le_sum (f := x) (fun i _ => h0 i) (by simp [hu])
    _ ≤ 1 := hd _

lemma plf_card_two (S : Finset V) (z : Sym2 V) (hz : ¬ z.IsDiag) (hS : z ∈ S.sym2) :
    (S.filter (fun v => v ∈ z)).card = 2 := by
  induction z using Sym2.ind with
  | h a b =>
    simp only [Sym2.mk_isDiag_iff] at hz
    rw [Finset.mk_mem_sym2_iff] at hS
    have : S.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v; simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro (rfl | rfl)
        · exact ⟨hS.1, Or.inl rfl⟩
        · exact ⟨hS.2, Or.inr rfl⟩
    rw [this, Finset.card_pair hz]

lemma plf_mv_sub (G : Graph V E) : matchingVectors G ⊆ matchingPolyhedron G := by
  intro x ⟨h01, hd⟩
  have h0 : ∀ e, 0 ≤ x e := fun e => by rcases h01 e with h | h <;> rw [h] <;> norm_num
  refine ⟨h0, hd, ?_⟩
  intro S r _ hS
  have key : 2 * insideSum G x S ≤ ∑ v ∈ S, degSum G x v := by
    unfold insideSum degSum
    rw [Finset.mul_sum]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro e _
    split_ifs with h
    · rw [← Finset.sum_filter, Finset.sum_const, plf_card_two S _ (G.loopless e) h]
      simp
    · apply Finset.sum_nonneg; intro v _; split_ifs <;> simp [h0 e]
  have hsum : ∑ v ∈ S, degSum G x v ≤ (S.card : ℝ) := by
    calc ∑ v ∈ S, degSum G x v ≤ ∑ v ∈ S, (1:ℝ) := Finset.sum_le_sum (fun v _ => hd v)
      _ = S.card := by simp
  have hk : insideSum G x S =
      (((Finset.univ.filter (fun e => G.ends e ∈ S.sym2)).filter (fun e => x e = 1)).card : ℝ) := by
    unfold insideSum
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e _
    rcases h01 e with h | h <;> simp [h]
  rw [hk] at key ⊢
  rw [hS] at hsum
  set k := ((Finset.univ.filter (fun e => G.ends e ∈ S.sym2)).filter (fun e => x e = 1)).card
  have : (2 * k : ℝ) ≤ 2 * r + 1 := by push_cast at hsum; linarith
  have : 2 * k ≤ 2 * r + 1 := by exact_mod_cast this
  exact_mod_cast (by omega : k ≤ r)

lemma plf_extreme (G : Graph V E) (x : E → ℝ) (hx : x ∈ matchingVectors G) :
    x ∈ Set.extremePoints ℝ (matchingPolyhedron G) := by
  rw [mem_extremePoints]
  refine ⟨plf_mv_sub G hx, ?_⟩
  intro x₁ h₁ x₂ h₂ hseg
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have key : ∀ e, x₁ e = (a • x₁ + b • x₂) e ∧ x₂ e = (a • x₁ + b • x₂) e := by
    intro e
    have l1 := plf_le_one G x₁ h₁ e
    have l2 := plf_le_one G x₂ h₂ e
    have p1 := h₁.1 e
    have p2 := h₂.1 e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hx.1 e with h | h <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    · have : x₁ e = 0 := by nlinarith
      have : x₂ e = 0 := by nlinarith
      constructor <;> simp [*]
    · have : x₁ e = 1 := by nlinarith
      have : x₂ e = 1 := by nlinarith
      constructor <;> simp [*]
  exact ⟨funext fun e => (key e).1, funext fun e => (key e).2⟩

theorem plf_core (G : Graph V E)
    (h : ∀ c : E → ℝ, ∃ x ∈ matchingPolyhedron G, (∀ e, x e = 0 ∨ x e = 1) ∧
      ∀ x' ∈ matchingPolyhedron G, W c x' ≤ W c x) :
    Set.extremePoints ℝ (matchingPolyhedron G) = matchingVectors G := by
  apply Set.Subset.antisymm
  · set T : Set (E → ℝ) := {x | x ∈ matchingPolyhedron G ∧ ∀ e, x e = 0 ∨ x e = 1} with hT
    have hTP : T ⊆ matchingPolyhedron G := fun x hx => hx.1
    have hTfin : T.Finite := by
      apply Set.Finite.subset (Set.Finite.pi (t := fun _ : E => ({0, 1} : Set ℝ))
        (fun _ => by simp))
      intro x hx e _
      rcases hx.2 e with h | h <;> simp [h]
    have hconv : Convex ℝ (matchingPolyhedron G) := by
      intro p hp q hq a b ha hb hab
      refine ⟨fun e => ?_, fun v => ?_, fun S r hr hS => ?_⟩
      · have := hp.1 e; have := hq.1 e
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
      · have h1 := hp.2.1 v; have h2 := hq.2.1 v
        have : degSum G (a • p + b • q) v = a * degSum G p v + b * degSum G q v := by
          unfold degSum; simp [Finset.sum_add_distrib, Finset.mul_sum]
        rw [this]; nlinarith
      · have h1 := hp.2.2 S r hr hS; have h2 := hq.2.2 S r hr hS
        have : insideSum G (a • p + b • q) S = a * insideSum G p S + b * insideSum G q S := by
          unfold insideSum; simp [Finset.sum_add_distrib, Finset.mul_sum]
        rw [this]; nlinarith
    have hPeq : matchingPolyhedron G = convexHull ℝ T := by
      apply Set.Subset.antisymm
      · intro x hx
        by_contra hnot
        obtain ⟨f, u, hf, hu⟩ := _root_.geometric_hahn_banach_closed_point (convex_convexHull ℝ T)
          (hTfin.isCompact_convexHull (𝕜 := ℝ) : IsCompact (convexHull ℝ T)).isClosed hnot
        let c : E → ℝ := fun e => f (Pi.single e 1)
        have hfW : ∀ y : E → ℝ, f y = W c y := by
          intro y
          conv_lhs => rw [← Finset.univ_sum_single y]
          rw [map_sum]
          unfold W
          apply Finset.sum_congr rfl
          intro e _
          have : Pi.single e (y e) = y e • (Pi.single e (1:ℝ) : E → ℝ) := by
            rw [← Pi.single_smul]; simp
          rw [this, map_smul, smul_eq_mul, mul_comm]
        obtain ⟨x0, hx0, h01, hmax⟩ := h c
        have h1 := hf x0 (subset_convexHull ℝ T ⟨hx0, h01⟩)
        have h2 := hmax x hx
        rw [hfW] at h1 hu
        linarith
      · exact convexHull_min hTP hconv
    rw [hPeq]
    intro x hx
    have := extremePoints_convexHull_subset hx
    exact ⟨this.2, this.1.2.1⟩
  · intro x hx
    exact plf_extreme G x hx

end EdmondsMatching65.Polyhedron

open EdmondsMatching65.Polyhedron


theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (h : ∀ c : E → ℝ, ∃ x ∈ matchingPolyhedron G, (∀ e, x e = 0 ∨ x e = 1) ∧
      ∀ x' ∈ matchingPolyhedron G, W c x' ≤ W c x) :
    Set.extremePoints ℝ (matchingPolyhedron G) = matchingVectors G := by
  exact plf_core G h
