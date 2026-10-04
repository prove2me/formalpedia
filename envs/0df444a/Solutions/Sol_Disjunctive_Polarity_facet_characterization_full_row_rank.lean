-- Prove2me | solution 1 for Disjunctive.Polarity.facet_characterization_full_row_rank
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:41:15.09834+00:00
-- url     : https://prove2.me/submissions/ca9370b1-386f-4397-98b2-ccaf15928e2f

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

open Disjunctive.Polarity

theorem solution : ¬ (∀ {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (Wt : Set ((Fin q → ℝ) × ℝ))
    (hFullDim : PolyDim (ProjOntoX (Poly2 A B b)) = (q : ℤ)) (hFullRowRank : B.rank = m)
    (hRepr : ProjOntoX (Poly2 A B b) = {x | ∀ v v0, (v, v0) ∈ Wt → dotProduct v x ≤ v0})
    (v : Fin q → ℝ) (v0 : ℝ),
    IsFacet (ProjOntoX (Poly2 A B b))
        (ProjOntoX (Poly2 A B b) ∩ {x | dotProduct v x = v0}) ↔
      IsExtremeRay Wt (v, v0)) := by
  intro h
  set A : Matrix (Fin 1) (Fin 0) ℝ := 0 with hA
  set b : Fin 1 → ℝ := 0 with hb
  set H : Set (Fin 1 → ℝ) := {x | x 0 ≤ 0} with hH
  have hP : ProjOntoX (Poly2 A (1 : Matrix (Fin 1) (Fin 1) ℝ) b) = H := by
    ext x
    simp only [ProjOntoX, Poly2, Set.mem_setOf_eq, hH]
    constructor
    · rintro ⟨u, hu⟩
      have := hu 0
      simpa [hA, hb] using this
    · intro hx
      refine ⟨0, fun i => ?_⟩
      rw [Subsingleton.elim i 0]
      simpa [hA, hb] using hx
  set Wt : Set ((Fin 1 → ℝ) × ℝ) := {z | ∃ t : ℝ, 0 ≤ t ∧ z = (fun _ => t, 0)} with hWt
  have hRepr : ProjOntoX (Poly2 A (1 : Matrix (Fin 1) (Fin 1) ℝ) b) =
      {x | ∀ v v0, (v, v0) ∈ Wt → dotProduct v x ≤ v0} := by
    rw [hP]
    ext x
    simp only [hH, hWt, Set.mem_setOf_eq]
    constructor
    · rintro hx v v0 ⟨t, ht, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp [dotProduct]
      nlinarith
    · intro hx
      have := hx (fun _ => 1) 0 ⟨1, zero_le_one, rfl⟩
      simpa [dotProduct] using this
  have hdim : PolyDim H = 1 := by
    have h0 : (0 : Fin 1 → ℝ) ∈ H := by simp [hH]
    have h1 : (fun _ => (-1 : ℝ)) ∈ H := by simp [hH]
    rw [PolyDim, if_pos ⟨0, h0⟩]
    have hmem := vsub_mem_vectorSpan ℝ h1 h0
    have hle : Module.finrank ℝ (vectorSpan ℝ H) ≤ 1 := by
      have := Submodule.finrank_le (vectorSpan ℝ H)
      simpa using this
    have hnz : Module.finrank ℝ (vectorSpan ℝ H) ≠ 0 := by
      intro hz
      rw [Submodule.finrank_eq_zero] at hz
      rw [hz] at hmem
      have := congrFun ((Submodule.mem_bot ℝ).mp hmem) 0
      simp at this
    have : Module.finrank ℝ (vectorSpan ℝ H) = 1 := by omega
    rw [this]; rfl
  have hF : H ∩ {x | dotProduct (fun _ => (-1 : ℝ)) x = 0} = {0} := by
    ext x
    simp only [hH, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, dotProduct,
      Finset.univ_unique, Finset.sum_singleton]
    constructor
    · rintro ⟨-, hx⟩; funext i; rw [Subsingleton.elim i 0]; simp [Fin.default_eq_zero] at hx
      simpa using hx
    · rintro rfl; simp
  have hfacet : IsFacet (ProjOntoX (Poly2 A (1 : Matrix (Fin 1) (Fin 1) ℝ) b))
      (ProjOntoX (Poly2 A (1 : Matrix (Fin 1) (Fin 1) ℝ) b) ∩
        {x | dotProduct (fun _ => (-1 : ℝ)) x = 0}) := by
    rw [hP, hF]
    refine ⟨⟨fun x hx => by rw [hx]; simp [hH], ?_⟩, Set.singleton_nonempty _, ?_⟩
    · rintro a ha c hc x hx ⟨s, t, hs, ht, hst, rfl⟩
      have hx0 := congrFun hx 0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx0
      simp only [hH, Set.mem_setOf_eq] at ha hc
      have : a 0 = 0 := by nlinarith
      funext i; rw [Subsingleton.elim i 0]; exact this
    · rw [hdim, PolyDim, if_pos (Set.singleton_nonempty _), vectorSpan_singleton, finrank_bot]
      norm_num
  have hFull : PolyDim (ProjOntoX (Poly2 A (1 : Matrix (Fin 1) (Fin 1) ℝ) b)) = ((1 : ℕ) : ℤ) := by
    rw [hP, hdim]; rfl
  have hray := (h A 1 b Wt hFull (by simp [Matrix.rank_one]) hRepr (fun _ => -1) 0).mp hfacet
  obtain ⟨-, ⟨t, ht, he⟩, -⟩ := hray
  have := congrFun (congrArg Prod.fst he) 0
  simp at this
  linarith

#print axioms solution
