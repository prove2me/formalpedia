-- Prove2me | solution 2 for AvramDividend.Classical.cross_sample_path_law_eq_of_all_finite_vector_laws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:44:51.462641+00:00
-- url     : https://prove2.me/submissions/5b7941e1-1d0b-4c38-aa81-a6db2f62e153

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_finite_cylinder_masses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω₁ Ω₂ ι : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (Y : Ω₁ → (ι → ℝ)) (Z : Ω₂ → (ι → ℝ))
    (hY : Measurable Y) (hZ : Measurable Z)
    (hP : P₁ univ ≠ ⊤)
    (hFinite : ∀ J : Finset ι,
      Measure.map (fun ω : Ω₁ => fun j : J => Y ω j.1) P₁ =
      Measure.map (fun ω : Ω₂ => fun j : J => Z ω j.1) P₂) :
    Measure.map Y P₁ = Measure.map Z P₂ := by
  apply cross_sample_path_law_eq_of_finite_cylinder_masses
    P₁ P₂ Y Z hY hZ hP
  intro J B hB
  let C : Set (J → ℝ) := Set.pi Set.univ (fun j : J => B j.1)
  have hC : MeasurableSet C := MeasurableSet.univ_pi (fun j => hB j.1 j.2)
  have hmY : Measurable (fun ω : Ω₁ => fun j : J => Y ω j.1) :=
    measurable_pi_iff.mpr (fun j => (measurable_pi_iff.mp hY) j.1)
  have hmZ : Measurable (fun ω : Ω₂ => fun j : J => Z ω j.1) :=
    measurable_pi_iff.mpr (fun j => (measurable_pi_iff.mp hZ) j.1)
  have heqY :
      (fun ω : Ω₁ => fun j : J => Y ω j.1) ⁻¹' C =
        Y ⁻¹' Set.pi (J : Set ι) B := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h i hi
      exact h ⟨i, hi⟩ (Set.mem_univ _)
    · intro h j hj
      exact h j.1 j.2
  have heqZ :
      (fun ω : Ω₂ => fun j : J => Z ω j.1) ⁻¹' C =
        Z ⁻¹' Set.pi (J : Set ι) B := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h i hi
      exact h ⟨i, hi⟩ (Set.mem_univ _)
    · intro h j hj
      exact h j.1 j.2
  calc
    P₁ (Y ⁻¹' Set.pi (J : Set ι) B) =
        (Measure.map (fun ω : Ω₁ => fun j : J => Y ω j.1) P₁) C := by
          rw [Measure.map_apply hmY hC]
          exact heqY.symm ▸ rfl
    _ = (Measure.map (fun ω : Ω₂ => fun j : J => Z ω j.1) P₂) C :=
        congrArg (fun m : Measure (J → ℝ) => m C) (hFinite J)
    _ = P₂ (Z ⁻¹' Set.pi (J : Set ι) B) := by
          rw [Measure.map_apply hmZ hC]
          exact heqZ ▸ rfl
