-- Prove2me | solution 1 for Disjunctive.Polarity.facet_characterization_via_transform
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:42:31.011987+00:00
-- url     : https://prove2.me/submissions/7dab8b8d-ee5d-4fbe-ac14-2ca6b191d21d

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_Transform

open Disjunctive.Polarity

theorem solution : ¬ (∀ {m p q w : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (Wt : Set ((Fin q → ℝ) × (Fin w → ℝ) × ℝ))
    (hFullDim : PolyDim (ProjOntoX (Poly2 A B b)) = (q : ℤ))
    (hWt_convex : Convex ℝ Wt)
    (hWt_cone : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Wt, t • z ∈ Wt)
    (hWt_pointed : ∀ z ∈ Wt, -z ∈ Wt → z = 0)
    (hRepr : ProjOntoX (Poly2 A B b) =
      {x | ∀ v ww v0, IsExtremeRay Wt (v, ww, v0) → dotProduct v x ≤ v0})
    (v : Fin q → ℝ) (v0 : ℝ),
    IsFacet (ProjOntoX (Poly2 A B b))
        (ProjOntoX (Poly2 A B b) ∩ {x | dotProduct v x = v0}) ↔
      IsExtremeRay (ProjVW Wt) (v, v0)) := by
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
  set Wt : Set ((Fin 1 → ℝ) × (Fin 0 → ℝ) × ℝ) :=
    {z | ∃ t : ℝ, 0 ≤ t ∧ z = (fun _ => t, 0, 0)} with hWt
  have hconv : Convex ℝ Wt := by
    rintro _ ⟨t1, ht1, rfl⟩ _ ⟨t2, ht2, rfl⟩ a c ha hc hac
    refine ⟨a * t1 + c * t2, by positivity, ?_⟩
    (ext i <;> simp) <;> exact i.elim0
  have hcone : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Wt, t • z ∈ Wt := by
    rintro t ht _ ⟨s, hs, rfl⟩
    exact ⟨t * s, by positivity, by (ext i <;> simp) <;> exact i.elim0⟩
  have hpointed : ∀ z ∈ Wt, -z ∈ Wt → z = 0 := by
    rintro _ ⟨s, hs, rfl⟩ ⟨r, hr, he⟩
    have := congrFun (congrArg Prod.fst he) 0
    simp at this
    have hs0 : s = 0 := by linarith
    subst hs0
    (ext i <;> simp) <;> exact i.elim0
  set z1 : (Fin 1 → ℝ) × (Fin 0 → ℝ) × ℝ := (fun _ => 1, 0, 0) with hz1
  have hray1 : IsExtremeRay Wt z1 := by
    refine ⟨fun h0 => by have := congrFun (congrArg Prod.fst h0) 0; simp [hz1] at this,
      ⟨1, zero_le_one, rfl⟩, ?_⟩
    have : {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • z1} = Wt := by
      ext x
      simp only [hWt, Set.mem_setOf_eq]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by (ext i <;> simp [hz1]) <;> exact i.elim0⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by (ext i <;> simp [hz1]) <;> exact i.elim0⟩
    rw [this]
    exact IsExtreme.refl ℝ Wt
  have hRepr : ProjOntoX (Poly2 A (1 : Matrix (Fin 1) (Fin 1) ℝ) b) =
      {x | ∀ v ww v0, IsExtremeRay Wt (v, ww, v0) → dotProduct v x ≤ v0} := by
    rw [hP]
    ext x
    simp only [hH, Set.mem_setOf_eq]
    constructor
    · rintro hx v ww v0 ⟨-, ⟨t, ht, he⟩, -⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -, rfl⟩ := he
      simp [dotProduct]
      nlinarith
    · intro hx
      have := hx (fun _ => 1) 0 0 hray1
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
  have hray := (h A 1 b Wt hFull hconv hcone hpointed hRepr (fun _ => -1) 0).mp hfacet
  obtain ⟨-, ⟨ww, t, ht, he⟩, -⟩ := hray
  have := congrFun (congrArg Prod.fst he) 0
  simp at this
  linarith

#print axioms solution
