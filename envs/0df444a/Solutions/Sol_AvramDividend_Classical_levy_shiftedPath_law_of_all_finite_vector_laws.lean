-- Prove2me | solution 1 for AvramDividend.Classical.levy_shiftedPath_law_of_all_finite_vector_laws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:31:36.235728+00:00
-- url     : https://prove2.me/submissions/e3e487cb-37a6-4ee1-8996-ba5b8b7bce9d

import Mathlib.Probability.Independence.Process.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Equality of all finite-dimensional shifted Lévy laws yields full path-law stationarity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (hFinite : ∀ J : Finset ℝ≥0,
      Measure.map (fun ω : Ω => fun j : J =>
        X.X (s + (j : ℝ≥0)) ω - X.X s ω) P =
      Measure.map (fun ω : Ω => fun j : J =>
        X.X (j : ℝ≥0) ω) P) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X (s + t) ω - X.X s ω
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro t
    exact ((X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl).sub
      ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hMass : (Measure.map Y P) Set.univ ≠ ⊤ := by
    simp [Measure.map_apply hY MeasurableSet.univ]
  change Measure.map Y P = Measure.map Z P
  apply piPathMeasure_eq_of_finite_cylinder_masses
    (Measure.map Y P) (Measure.map Z P) hMass
  intro J B hB
  let F : Set (J → ℝ) := Set.pi Set.univ (fun i : J => B i)
  have hF : MeasurableSet F := by
    exact MeasurableSet.pi Set.countable_univ
      (fun i hi => hB i (Finset.mem_coe.mp i.property))
  have hSet : MeasurableSet (Set.pi (J : Set ℝ≥0) B) := by
    exact MeasurableSet.pi J.countable_toSet
      (fun i hi => hB i (Finset.mem_coe.mp hi))
  have hYJ : Measurable (fun ω : Ω => fun i : J => Y ω i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (i : ℝ≥0)).comp hY
  have hZJ : Measurable (fun ω : Ω => fun i : J => Z ω i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (i : ℝ≥0)).comp hZ
  have hPreY :
      Y ⁻¹' Set.pi (J : Set ℝ≥0) B =
        (fun ω : Ω => fun i : J => Y ω i) ⁻¹' F := by
    ext ω
    simp [F, Set.mem_pi]
  have hPreZ :
      Z ⁻¹' Set.pi (J : Set ℝ≥0) B =
        (fun ω : Ω => fun i : J => Z ω i) ⁻¹' F := by
    ext ω
    simp [F, Set.mem_pi]
  calc
    (Measure.map Y P) (Set.pi (J : Set ℝ≥0) B) =
        P (Y ⁻¹' Set.pi (J : Set ℝ≥0) B) :=
      Measure.map_apply hY hSet
    _ = P ((fun ω : Ω => fun i : J => Y ω i) ⁻¹' F) := by rw [hPreY]
    _ = (Measure.map (fun ω : Ω => fun i : J => Y ω i) P) F :=
      (Measure.map_apply hYJ hF).symm
    _ = (Measure.map (fun ω : Ω => fun i : J => Z ω i) P) F := by
      rw [show Measure.map (fun ω : Ω => fun i : J => Y ω i) P =
               Measure.map (fun ω : Ω => fun i : J => Z ω i) P from hFinite J]
    _ = P ((fun ω : Ω => fun i : J => Z ω i) ⁻¹' F) :=
      Measure.map_apply hZJ hF
    _ = P (Z ⁻¹' Set.pi (J : Set ℝ≥0) B) := by rw [hPreZ]
    _ = (Measure.map Z P) (Set.pi (J : Set ℝ≥0) B) :=
      (Measure.map_apply hZ hSet).symm
