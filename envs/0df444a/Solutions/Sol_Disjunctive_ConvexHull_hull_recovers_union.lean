-- Prove2me | solution 1 for Disjunctive.ConvexHull.hull_recovers_union
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:41:08.743269+00:00
-- url     : https://prove2.me/submissions/85d10307-169a-403b-9ebb-7732a08172d0

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

set_option autoImplicit false

namespace Disjunctive.ConvexHull.E117725c

open Disjunctive.ConvexHull

lemma rec_mono {m₁ m₂ n : ℕ} (A₁ : Matrix (Fin m₁) (Fin n) ℝ) (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ) (b₂ : Fin m₂ → ℝ)
    (hne : (Poly A₁ b₁).Nonempty) (hsub : Poly A₁ b₁ ⊆ Poly A₂ b₂) :
    RecessionCone A₁ ⊆ RecessionCone A₂ := by
  obtain ⟨x0, hx0⟩ := hne
  intro y hy
  have key : ∀ t : ℝ, 0 ≤ t → ∀ i, b₂ i ≤ (A₂.mulVec x0) i + t * (A₂.mulVec y) i := by
    intro t ht
    have hmem : x0 + t • y ∈ Poly A₂ b₂ := by
      apply hsub
      intro i
      have h1 : b₁ i ≤ (A₁.mulVec x0) i := hx0 i
      have h2 : (0 : Fin m₁ → ℝ) i ≤ (A₁.mulVec y) i := hy i
      rw [Pi.zero_apply] at h2
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    intro i
    have := hmem i
    rw [Matrix.mulVec_add, Matrix.mulVec_smul] at this
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  show (0 : Fin m₂ → ℝ) ≤ A₂.mulVec y
  intro i
  rw [Pi.zero_apply]
  by_contra hc
  push Not at hc
  have h0 := key 0 le_rfl i
  have ht : 0 ≤ ((A₂.mulVec x0) i - b₂ i + 1) / (-(A₂.mulVec y) i) :=
    div_nonneg (by linarith) (by linarith)
  have h1 := key _ ht i
  have hne : (A₂.mulVec y) i ≠ 0 := ne_of_lt hc
  have heq : ((A₂.mulVec x0) i - b₂ i + 1) / (-(A₂.mulVec y) i) * (A₂.mulVec y) i
      = -((A₂.mulVec x0) i - b₂ i + 1) := by
    field_simp
  linarith

lemma exists_max {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (k : Q) (hk : k ∈ FeasibleIndices m A b) :
    ∃ j ∈ MaximalIndices m A b, Poly (A k) (b k) ⊆ Poly (A j) (b j) := by
  classical
  have hs : ((fun h => Poly (A h) (b h)) '' FeasibleIndices m A b).Finite :=
    (Set.toFinite _).image _
  obtain ⟨M, hkM, hM⟩ := hs.exists_le_maximal (a := Poly (A k) (b k)) ⟨k, hk, rfl⟩
  obtain ⟨j, hj, rfl⟩ := hM.1
  refine ⟨j, ⟨hj, fun i hi hji => ?_⟩, hkM⟩
  exact hM.2 ⟨i, hi, rfl⟩ hji

end Disjunctive.ConvexHull.E117725c

open Disjunctive.ConvexHull in
theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (h25 : ∀ h ∈ MaximalIndices m A b, ∀ j ∈ MaximalIndices m A b, RecessionCone (A h) = RecessionCone (A j))
    (h26 : ∀ k, k ∉ FeasibleIndices m A b → ∀ h ∈ MaximalIndices m A b,
             RecessionCone (A k) ⊆ RecessionCone (A h)) :
    ProjX (IntegerRestricted (LiftedPolyhedron m A b Set.univ)) = DisjunctiveSet m A b := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨⟨y, y0⟩, ⟨hx, hcon, -, hsum⟩, hint⟩
    simp only at hx hcon hsum hint
    have hk : ∃ k, y0 k = 1 := by
      by_contra hne
      push Not at hne
      have hz : ∀ h, y0 h = 0 := fun h => (hint h).resolve_right (hne h)
      simp [hz] at hsum
    obtain ⟨k, hk⟩ := hk
    have huniq : ∀ h, h ≠ k → y0 h = 0 := by
      intro h hh
      rcases hint h with h0 | h1
      · exact h0
      · exfalso
        have hle : ∑ g ∈ ({h, k} : Finset Q), y0 g ≤ ∑ g, y0 g :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun g _ _ => (hcon g (Set.mem_univ g)).2)
        rw [Finset.sum_pair hh, h1, hk, hsum] at hle
        norm_num at hle
    have hyk : y k ∈ Poly (A k) (b k) := by
      intro i
      have := (hcon k (Set.mem_univ k)).1 i
      simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hk, one_mul] at this
      linarith
    obtain ⟨j, hjmax, hkj⟩ := E117725c.exists_max m A b k ⟨_, hyk⟩
    have hC : ∀ h, RecessionCone (A h) ⊆ RecessionCone (A j) := by
      intro h
      by_cases hf : h ∈ FeasibleIndices m A b
      · obtain ⟨j', hj', hhj'⟩ := E117725c.exists_max m A b h hf
        rw [← h25 j' hj' j hjmax]
        exact E117725c.rec_mono _ _ _ _ hf hhj'
      · exact h26 h hf j hjmax
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    have hterm : ∀ h, ∀ i, y0 h * b j i ≤ (A j).mulVec (y h) i := by
      intro h i
      by_cases hh : h = k
      · subst hh
        rw [hk, one_mul]
        exact hkj hyk i
      · rw [huniq h hh, zero_mul]
        have hyh : y h ∈ RecessionCone (A h) := by
          show (0 : Fin (m h) → ℝ) ≤ (A h).mulVec (y h)
          intro i'
          have := (hcon h (Set.mem_univ h)).1 i'
          simpa only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, huniq h hh,
            zero_mul, sub_zero] using this
        have := hC h hyh
        have h2 : (0 : Fin (m j) → ℝ) i ≤ (A j).mulVec (y h) i := this i
        simpa using h2
    intro i
    rw [hx, Matrix.mulVec_sum, Finset.sum_apply]
    calc b j i = ∑ h, y0 h * b j i := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ h, (A j).mulVec (y h) i := Finset.sum_le_sum (fun h _ => hterm h i)
  · intro x hx
    obtain ⟨h, hxh⟩ := Set.mem_iUnion.1 hx
    refine ⟨(fun g => if g = h then x else 0, fun g => if g = h then (1 : ℝ) else 0),
      ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩⟩
    · simp
    · intro g _
      by_cases hg : g = h
      · subst hg
        simp only [if_true, one_smul]
        refine ⟨?_, zero_le_one⟩
        intro i
        have := hxh i
        simp only [Pi.zero_apply, Pi.sub_apply]
        linarith
      · simp [hg]
    · intro g hg
      exact absurd (Set.mem_univ g) hg
    · simp
    · intro g
      by_cases hg : g = h <;> simp [hg]
