-- Prove2me | solution 1 for AvramDividend.Classical.levy_shiftedConsecutiveIncrement_vector_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:31:33.946514+00:00
-- url     : https://prove2.me/submissions/dc1ff105-f58a-49bc-839d-7c7ab622f6e4

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_shifted_increment_rectangle_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Finite vectors of consecutive Lévy increments have the same law after a deterministic time shift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω) P =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (Fin n → ℝ) := fun ω i =>
    X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω
  let Z : Ω → (Fin n → ℝ) := fun ω i =>
    X.X (t (i.val + 1)) ω - X.X (t i.val) ω
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((X.adapted (s + t (i.val + 1))).mono
      (𝓕.le (s + t (i.val + 1))) le_rfl).sub
      ((X.adapted (s + t i.val)).mono (𝓕.le (s + t i.val)) le_rfl)
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((X.adapted (t (i.val + 1))).mono
      (𝓕.le (t (i.val + 1))) le_rfl).sub
      ((X.adapted (t i.val)).mono (𝓕.le (t i.val)) le_rfl)
  have hMass : (Measure.map Y P) Set.univ ≠ ⊤ := by
    simp [Measure.map_apply hY MeasurableSet.univ]
  change Measure.map Y P = Measure.map Z P
  apply piPathMeasure_eq_of_finite_cylinder_masses
    (Measure.map Y P) (Measure.map Z P) hMass
  intro J B hB
  let D : Fin n → Set ℝ := fun i => if i ∈ J then B i else Set.univ
  have hD : ∀ i, MeasurableSet (D i) := by
    intro i
    dsimp [D]
    split_ifs with hi
    · exact hB i hi
    · exact MeasurableSet.univ
  have hCylinder :
      Set.pi (J : Set (Fin n)) B = Set.pi Set.univ D := by
    ext y
    simp only [Set.mem_pi, Finset.mem_coe, Set.mem_univ, forall_true_left]
    constructor
    · intro h i
      change y i ∈ D i
      by_cases hj : i ∈ J
      · simpa [D, hj] using h i hj
      · simp [D, hj]
    · intro h i hi
      have hh := h i
      simpa [D, hi] using hh
  have hCylinderMeas : MeasurableSet (Set.pi (J : Set (Fin n)) B) :=
    MeasurableSet.pi J.countable_toSet
      (by intro i hi; exact hB i (Finset.mem_coe.mp hi))
  rw [Measure.map_apply hY hCylinderMeas,
      Measure.map_apply hZ hCylinderMeas,
      hCylinder]
  exact levy_finitePrefix_shifted_increment_rectangle_eq X s t ht n D hD
