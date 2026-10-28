-- Prove2me | solution 1 for AvramDividend.Classical.piPathMeasure_map_eq_of_finite_pushforwards
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:41:58.146156+00:00
-- url     : https://prove2.me/submissions/571a4aa2-63e0-49aa-a523-96818848d7f9

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open AvramDividend.Classical

/-- Arbitrary measurable path-valued pushforwards agree when every finite-coordinate pushforward agrees. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {μ ν : Measure Ω}
    (Y Z : Ω → (ι → ℝ))
    (hY : Measurable Y) (hZ : Measurable Z)
    (hMass : (Measure.map Y μ) Set.univ ≠ ⊤)
    (hFinite : ∀ J : Finset ι,
      Measure.map (fun ω : Ω => fun j : J => Y ω j) μ =
      Measure.map (fun ω : Ω => fun j : J => Z ω j) ν) :
    Measure.map Y μ = Measure.map Z ν := by
  classical
  apply piPathMeasure_eq_of_finite_cylinder_masses
    (Measure.map Y μ) (Measure.map Z ν) hMass
  intro J B hB
  let F : Set (J → ℝ) := Set.pi Set.univ (fun i : J => B i)
  have hF : MeasurableSet F := by
    exact MeasurableSet.pi Set.countable_univ
      (fun i hi => hB i (Finset.mem_coe.mp i.property))
  have hSet : MeasurableSet (Set.pi (J : Set ι) B) := by
    exact MeasurableSet.pi J.countable_toSet
      (fun i hi => hB i (Finset.mem_coe.mp hi))
  have hYJ : Measurable (fun ω : Ω => fun i : J => Y ω i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (i : ι)).comp hY
  have hZJ : Measurable (fun ω : Ω => fun i : J => Z ω i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (i : ι)).comp hZ
  have hPreY :
      Y ⁻¹' Set.pi (J : Set ι) B =
        (fun ω : Ω => fun i : J => Y ω i) ⁻¹' F := by
    ext ω
    simp [F, Set.mem_pi]
  have hPreZ :
      Z ⁻¹' Set.pi (J : Set ι) B =
        (fun ω : Ω => fun i : J => Z ω i) ⁻¹' F := by
    ext ω
    simp [F, Set.mem_pi]
  calc
    (Measure.map Y μ) (Set.pi (J : Set ι) B) =
        μ (Y ⁻¹' Set.pi (J : Set ι) B) :=
      Measure.map_apply hY hSet
    _ = μ ((fun ω : Ω => fun i : J => Y ω i) ⁻¹' F) := by rw [hPreY]
    _ = (Measure.map (fun ω : Ω => fun i : J => Y ω i) μ) F :=
      (Measure.map_apply hYJ hF).symm
    _ = (Measure.map (fun ω : Ω => fun i : J => Z ω i) ν) F := by
      rw [hFinite J]
    _ = ν ((fun ω : Ω => fun i : J => Z ω i) ⁻¹' F) :=
      Measure.map_apply hZJ hF
    _ = ν (Z ⁻¹' Set.pi (J : Set ι) B) := by rw [hPreZ]
    _ = (Measure.map Z ν) (Set.pi (J : Set ι) B) :=
      (Measure.map_apply hZ hSet).symm
