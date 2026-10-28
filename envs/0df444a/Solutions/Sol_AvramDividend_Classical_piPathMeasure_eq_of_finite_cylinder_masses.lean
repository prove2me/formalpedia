-- Prove2me | solution 1 for AvramDividend.Classical.piPathMeasure_eq_of_finite_cylinder_masses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:25:39.971994+00:00
-- url     : https://prove2.me/submissions/9f86d602-02d8-4db4-834e-834afce91a1a

import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
/-- Probability path laws agree if they agree on every finite-coordinate cylinder. -/
theorem solution
    {ι : Type*} (μ ν : Measure (ι → ℝ))
    (hFinite : μ Set.univ ≠ ⊤)
    (hCyl : ∀ (J : Finset ι) (B : ι → Set ℝ),
      (∀ i ∈ J, MeasurableSet (B i)) →
      μ (Set.pi (J : Set ι) B) = ν (Set.pi (J : Set ι) B)) :
    μ = ν := by
  classical
  let C : Set (Set (ι → ℝ)) := {S | ∃ (J : Finset ι) (B : ι → Set ℝ),
      (∀ i ∈ J, MeasurableSet (B i)) ∧ S = Set.pi (J : Set ι) B}
  have hPi : IsPiSystem C := by
    intro S hS T hT; rcases hS with ⟨J, B, hB, rfl⟩; rcases hT with ⟨K, D, hD, rfl⟩
    let E : ι → Set ℝ := fun i => (if i ∈ J then B i else Set.univ) ∩ (if i ∈ K then D i else Set.univ)
    intro hNonempty
    refine ⟨J ∪ K, E, ?_, ?_⟩
    · intro i hi; dsimp [E]
      apply MeasurableSet.inter
      · split_ifs with hj
        · exact hB i hj
        · exact MeasurableSet.univ
      · split_ifs with hk
        · exact hD i hk
        · exact MeasurableSet.univ
    · ext y
      simp only [Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe]
      constructor
      · rintro ⟨hJ, hK⟩ i hi; have hi' : i ∈ J ∨ i ∈ K := Finset.mem_union.mp hi
        change y i ∈ E i
        dsimp [E]
        constructor
        · split_ifs with hj
          · exact hJ i hj
          · trivial
        · split_ifs with hk
          · exact hK i hk
          · trivial
      · intro h
        constructor
        · intro i hi; have hu : i ∈ J ∪ K := Finset.mem_union.mpr (Or.inl hi)
          have hh := h i hu; exact (show y i ∈ B i from by simpa [E, hi] using hh.1)
        · intro i hi; have hu : i ∈ J ∪ K := Finset.mem_union.mpr (Or.inr hi)
          have hh := h i hu; exact (show y i ∈ D i from by simpa [E, hi] using hh.2)
  have hSub : {S : Set (ι → ℝ) | ∃ i A, MeasurableSet A ∧ Function.eval i ⁻¹' A = S} ⊆ C := by
    rintro S ⟨i, A, hA, rfl⟩
    refine ⟨{i}, (fun _ => A), ?_, ?_⟩
    · intro j hj; exact hA
    · ext y; simp [Set.mem_pi]
  have hGen : (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)) = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · rw [MeasurableSpace.pi_eq_generateFrom_projections]
      exact MeasurableSpace.generateFrom_mono hSub
    · apply MeasurableSpace.generateFrom_le
      rintro S ⟨J, B, hB, rfl⟩; exact MeasurableSet.pi J.countable_toSet (by
        intro i hi; exact hB i (Finset.mem_coe.mp hi))
  let cover : ℕ → Set (ι → ℝ) := fun _ => Set.univ
  have hCover : (⋃ n, cover n) = Set.univ := by
    ext ω; simp [cover]
  have hCoverC : ∀ n, cover n ∈ C := by
    intro n; refine ⟨∅, (fun _ => Set.univ), ?_, ?_⟩
    · simp
    · simp [cover, Set.pi]
  have hCoverFinite : ∀ n, μ (cover n) ≠ ⊤ := by
    intro n; simpa [cover] using hFinite
  have hAgree : ∀ S ∈ C, μ S = ν S := by
    rintro S ⟨J, B, hB, rfl⟩; exact hCyl J B hB
  exact Measure.ext_of_generateFrom_of_iUnion C cover hGen hPi hCover hCoverC hCoverFinite hAgree
