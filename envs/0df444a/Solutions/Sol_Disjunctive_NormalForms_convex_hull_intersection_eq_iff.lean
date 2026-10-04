-- Prove2me | solution 1 for Disjunctive.NormalForms.convex_hull_intersection_eq_iff
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:36:51.665982+00:00
-- url     : https://prove2.me/submissions/e34eb2a6-b988-458f-ae15-22cbf777d3de

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

open Disjunctive.NormalForms

theorem solution : ¬ (∀ {n : ℕ} {Q1 Q2 : Type} [Fintype Q1] [Fintype Q2]
    (m1 : Q1 → ℕ) (A1 : (i : Q1) → Matrix (Fin (m1 i)) (Fin n) ℝ) (b1 : (i : Q1) → Fin (m1 i) → ℝ)
    (m2 : Q2 → ℕ) (A2 : (i : Q2) → Matrix (Fin (m2 i)) (Fin n) ℝ) (b2 : (i : Q2) → Fin (m2 i) → ℝ) ,
    closure (convexHull ℝ
          ((⋃ i : Q1, Disjunctive.NormalForms.Poly (A1 i) (b1 i)) ∩ (⋃ i : Q2, Disjunctive.NormalForms.Poly (A2 i) (b2 i)))) =
        closure (convexHull ℝ (⋃ i : Q1, Disjunctive.NormalForms.Poly (A1 i) (b1 i))) ∩
          closure (convexHull ℝ (⋃ i : Q2, Disjunctive.NormalForms.Poly (A2 i) (b2 i))) ↔
      (∀ x ∈ Set.extremePoints ℝ
            (closure (convexHull ℝ (⋃ i : Q1, Disjunctive.NormalForms.Poly (A1 i) (b1 i))) ∩
              closure (convexHull ℝ (⋃ i : Q2, Disjunctive.NormalForms.Poly (A2 i) (b2 i)))),
          ∃ i k, x ∈ Set.extremePoints ℝ (Disjunctive.NormalForms.Poly (A1 i) (b1 i) ∩ Disjunctive.NormalForms.Poly (A2 k) (b2 k))) ∧
        (∀ y ∈ ExtremeDirections
              (closure (convexHull ℝ (⋃ i : Q1, Disjunctive.NormalForms.Poly (A1 i) (b1 i))) ∩
                closure (convexHull ℝ (⋃ i : Q2, Disjunctive.NormalForms.Poly (A2 i) (b2 i)))),
            ∃ i k, y ∈ ExtremeDirections (Disjunctive.NormalForms.Poly (A1 i) (b1 i) ∩ Disjunctive.NormalForms.Poly (A2 k) (b2 k)))) := by
  intro h
  set m1 : Fin 2 → ℕ := fun _ => 1 with hm1
  set A1 : (i : Fin 2) → Matrix (Fin (m1 i)) (Fin 2) ℝ :=
    fun i => if i = 0 then !![-1, 0] else !![1, 0] with hA1
  set b1 : (i : Fin 2) → Fin (m1 i) → ℝ := fun i => if i = 0 then ![0] else ![2] with hb1
  set m2 : Fin 1 → ℕ := fun _ => 2 with hm2
  set A2 : (i : Fin 1) → Matrix (Fin (m2 i)) (Fin 2) ℝ := fun _ => !![1, 0; -1, 0] with hA2
  set b2 : (i : Fin 1) → Fin (m2 i) → ℝ := fun _ => ![1, -1] with hb2
  have hU1 : ∀ x : Fin 2 → ℝ, x ∈ (⋃ i : Fin 2, Disjunctive.NormalForms.Poly (A1 i) (b1 i)) ↔
      x 0 ≤ 0 ∨ 2 ≤ x 0 := by
    intro x
    simp only [Set.mem_iUnion, Disjunctive.NormalForms.Poly, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi⟩
      have := hi 0
      fin_cases i <;> simp [hA1, hb1, Matrix.mulVec, dotProduct] at this
      · left; linarith
      · right; linarith
    · rintro (hx | hx)
      · exact ⟨0, fun r => by fin_cases r; simp [hA1, hb1, Matrix.mulVec, dotProduct]; linarith⟩
      · exact ⟨1, fun r => by fin_cases r; simp [hA1, hb1, Matrix.mulVec, dotProduct]; linarith⟩
  have hU2 : ∀ x : Fin 2 → ℝ, x ∈ (⋃ i : Fin 1, Disjunctive.NormalForms.Poly (A2 i) (b2 i)) ↔
      x 0 = 1 := by
    intro x
    simp only [Set.mem_iUnion, Disjunctive.NormalForms.Poly, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi⟩
      have h0 := hi 0
      have h1 := hi 1
      simp [hA2, hb2, Matrix.mulVec, dotProduct] at h0 h1
      linarith
    · intro hx
      exact ⟨0, fun r => by fin_cases r <;> simp [hA2, hb2, Matrix.mulVec, dotProduct, hx]⟩
  set L : Set (Fin 2 → ℝ) := {x | x 0 = 1} with hL
  have hLconv : Convex ℝ L := by
    intro a ha b hb s t hs ht hst
    simp only [hL, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hb ⊢
    rw [ha, hb]; linarith
  have hLclosed : IsClosed L := isClosed_eq (continuous_apply 0) continuous_const
  have hU2L : (⋃ i : Fin 1, Disjunctive.NormalForms.Poly (A2 i) (b2 i)) = L := by
    ext x; rw [hU2]; rfl
  set Sset := closure (convexHull ℝ (⋃ i : Fin 2, Disjunctive.NormalForms.Poly (A1 i) (b1 i))) ∩
    closure (convexHull ℝ (⋃ i : Fin 1, Disjunctive.NormalForms.Poly (A2 i) (b2 i))) with hS
  have hSL : Sset = L := by
    rw [hS, hU2L, hLconv.convexHull_eq, hLclosed.closure_eq]
    apply Set.inter_eq_right.mpr
    intro x hx
    apply subset_closure
    have hp : (fun i => if i = 0 then (0 : ℝ) else x 1) ∈
        (⋃ i : Fin 2, Disjunctive.NormalForms.Poly (A1 i) (b1 i)) := by
      rw [hU1]; left; simp
    have hq : (fun i => if i = 0 then (2 : ℝ) else x 1) ∈
        (⋃ i : Fin 2, Disjunctive.NormalForms.Poly (A1 i) (b1 i)) := by
      rw [hU1]; right; simp
    apply segment_subset_convexHull hp hq
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext i; fin_cases i
    · simp [hL] at hx ⊢ <;> linarith
    · simp; ring
  set e : Fin 2 → ℝ := ![0, 1] with he
  have hmemL : ∀ x ∈ L, ∀ t : ℝ, x + t • e ∈ L := by
    intro x hx t; simp [hL, he] at hx ⊢; exact hx
  have hrhs1 : ∀ x ∈ Set.extremePoints ℝ Sset,
      ∃ i k, x ∈ Set.extremePoints ℝ (Disjunctive.NormalForms.Poly (A1 i) (b1 i) ∩
        Disjunctive.NormalForms.Poly (A2 k) (b2 k)) := by
    intro x hx
    exfalso
    rw [hSL] at hx
    obtain ⟨hxL, hext⟩ := hx
    have := hext (hmemL x hxL (-1)) (hmemL x hxL 1)
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
        funext i; simp; ring⟩
    have h1 := congrFun this 1
    simp [he] at h1
  have hrhs2 : ∀ y ∈ ExtremeDirections Sset,
      ∃ i k, y ∈ ExtremeDirections (Disjunctive.NormalForms.Poly (A1 i) (b1 i) ∩
        Disjunctive.NormalForms.Poly (A2 k) (b2 k)) := by
    intro y hy
    exfalso
    obtain ⟨hy0, hyR, hext⟩ := hy
    rw [hSL] at hyR hext
    have hp : (![1, 0] : Fin 2 → ℝ) ∈ L := by simp [hL]
    have hy1 : y 0 = 0 := by
      have := hyR _ hp 1 zero_le_one
      simp [hL] at this; simpa [Matrix.vecHead] using this
    have hneg : -y ∈ RecessionCone2 L := by
      intro x hx t ht
      simp [hL] at hx ⊢; rw [hx, hy1]; simp
    have h0ray : (0 : Fin 2 → ℝ) ∈ {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • y} := ⟨0, le_rfl, by simp⟩
    have := hext.2 hneg hyR h0ray ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      funext i; simp <;> ring⟩
    obtain ⟨t, ht, hty⟩ := this
    apply hy0
    have : (1 + t) • y = 0 := by rw [add_smul, one_smul, ← hty]; simp
    rcases smul_eq_zero.mp this with h' | h'
    · linarith
    · exact h'
  have hlhs := (h m1 A1 b1 m2 A2 b2).mpr ⟨hrhs1, hrhs2⟩
  have hempty : (⋃ i : Fin 2, Disjunctive.NormalForms.Poly (A1 i) (b1 i)) ∩
      (⋃ i : Fin 1, Disjunctive.NormalForms.Poly (A2 i) (b2 i)) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, hU1, hU2, Set.mem_empty_iff_false, iff_false, not_and]
    rintro (hx | hx) hx' <;> linarith
  rw [hempty, convexHull_empty, closure_empty] at hlhs
  have hpt : (![1, 0] : Fin 2 → ℝ) ∈ L := by simp [hL]
  rw [← hSL, hS, ← hlhs] at hpt
  exact hpt

#print axioms solution
