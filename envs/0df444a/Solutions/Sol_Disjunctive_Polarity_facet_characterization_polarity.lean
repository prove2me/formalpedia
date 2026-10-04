-- Prove2me | solution 1 for Disjunctive.Polarity.facet_characterization_polarity
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:40:16.421054+00:00
-- url     : https://prove2.me/submissions/ad0dc48f-a0c9-4dfc-a9a4-f6b2abcaceda

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_Polars

open Disjunctive.Polarity

theorem solution : ¬ (∀ {n : ℕ} {Q : Type} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (hdim : PolyDim (DisjunctiveSet m A b) = (n : ℤ)) (α : Fin n → ℝ) (α0 : ℝ) (hα0 : α0 ≠ 0),
    IsFacet (closure (convexHull ℝ (DisjunctiveSet m A b)))
        (closure (convexHull ℝ (DisjunctiveSet m A b)) ∩ {x | dotProduct α x = α0}) ↔
      IsExtremeRay (W0 m A b) (α, α0)) := by
  intro h
  set A : Fin 1 → Matrix (Fin 2) (Fin 1) ℝ := fun _ => !![1; -1] with hA
  set b : Fin 1 → Fin 2 → ℝ := fun _ => ![0, -1] with hb
  set I01 : Set (Fin 1 → ℝ) := {x | 0 ≤ x 0 ∧ x 0 ≤ 1} with hI
  have hD : DisjunctiveSet (fun _ : Fin 1 => 2) A b = I01 := by
    ext x
    simp only [DisjunctiveSet, Set.mem_iUnion, Disjunctive.Polarity.Poly, Set.mem_setOf_eq, hI]
    constructor
    · rintro ⟨i, hi⟩
      have h0 := hi 0
      have h1 := hi 1
      simp [hA, hb, Matrix.mulVec, dotProduct] at h0 h1
      exact ⟨h0, by linarith⟩
    · rintro ⟨h0, h1⟩
      exact ⟨0, fun r => by fin_cases r <;> simp [hA, hb, Matrix.mulVec, dotProduct] <;> linarith⟩
  have hIconv : Convex ℝ I01 := by
    intro x hx y hy s t hs ht hst
    simp only [hI, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    constructor <;> nlinarith
  have hIclosed : IsClosed I01 :=
    (isClosed_le continuous_const (continuous_apply 0)).inter
      (isClosed_le (continuous_apply 0) continuous_const)
  have hcl : closure (convexHull ℝ (DisjunctiveSet (fun _ : Fin 1 => 2) A b)) = I01 := by
    rw [hD, hIconv.convexHull_eq, hIclosed.closure_eq]
  have hdimI : PolyDim I01 = 1 := by
    have hne : I01.Nonempty := ⟨0, by simp [hI]⟩
    rw [PolyDim, if_pos hne]
    have h1 : (fun _ => (1 : ℝ)) ∈ I01 := by simp [hI]
    have h0 : (0 : Fin 1 → ℝ) ∈ I01 := by simp [hI]
    have hmem := vsub_mem_vectorSpan ℝ h1 h0
    have hle : Module.finrank ℝ (vectorSpan ℝ I01) ≤ 1 := by
      have := Submodule.finrank_le (vectorSpan ℝ I01)
      simpa using this
    have hnz : Module.finrank ℝ (vectorSpan ℝ I01) ≠ 0 := by
      intro hz
      rw [Submodule.finrank_eq_zero] at hz
      rw [hz] at hmem
      have := congrFun ((Submodule.mem_bot ℝ).mp hmem) 0
      simp at this
    have : Module.finrank ℝ (vectorSpan ℝ I01) = 1 := by omega
    rw [this]; rfl
  have hF : I01 ∩ {x | dotProduct (fun _ => (1 : ℝ)) x = 1} = {fun _ => 1} := by
    ext x
    simp only [hI, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, dotProduct,
      Finset.univ_unique, Finset.sum_singleton, one_mul]
    constructor
    · rintro ⟨-, hx⟩; funext i; rw [Subsingleton.elim i 0]; simpa [Fin.default_eq_zero] using hx
    · rintro rfl; simp
  have hfacet : IsFacet (closure (convexHull ℝ (DisjunctiveSet (fun _ : Fin 1 => 2) A b)))
      (closure (convexHull ℝ (DisjunctiveSet (fun _ : Fin 1 => 2) A b)) ∩
        {x | dotProduct (fun _ => (1 : ℝ)) x = 1}) := by
    rw [hcl, hF]
    refine ⟨⟨fun x hx => by rw [hx]; simp [hI], ?_⟩, Set.singleton_nonempty _, ?_⟩
    · rintro a ha c hc x hx ⟨s, t, hs, ht, hst, rfl⟩
      have hx0 := congrFun hx 0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx0
      have : a 0 = 1 := by nlinarith [ha.1, ha.2, hc.1, hc.2]
      funext i; rw [Subsingleton.elim i 0]; exact this
    · rw [hdimI, PolyDim, if_pos (Set.singleton_nonempty _), vectorSpan_singleton, finrank_bot]
      norm_num
  have hray := (h (fun _ : Fin 1 => 2) A b (by rw [hD, hdimI]; rfl) (fun _ => 1) 1 one_ne_zero).mp hfacet
  obtain ⟨-, ⟨u, hu⟩, -⟩ := hray
  have hfeas : (0 : Fin 1) ∈ FeasibleIndices (fun _ : Fin 1 => 2) A b := by
    refine ⟨0, fun r => ?_⟩
    fin_cases r <;> simp [hA, hb, Matrix.mulVec, dotProduct]
  obtain ⟨hvec, hval, hnn⟩ := hu 0 hfeas
  have e := congrFun hvec 0
  simp [hA, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at e
  simp [hb, dotProduct, Fin.sum_univ_two] at hval
  have := hnn 1
  simp at this
  linarith

#print axioms solution
