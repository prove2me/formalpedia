-- Prove2me | solution 1 for FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:48.262239+00:00
-- url     : https://prove2.me/submissions/781f47da-fa7d-4910-afb1-891c3e8030f3

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport
import Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_readable

open MeasureTheory
open scoped RealInnerProductSpace
section FiniteMeasureHalfspace
/-- Uniform positive mass, at most the total mass, of the strict open halfspaces through an interior point of the convex
hull of the support of a finite Borel measure. -/
theorem solution {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ μ.support)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ μ.real Set.univ ∧ ∀ u : E, ‖u‖ = 1 → m ≤ μ.real {x | 0 < ⟪u, x - x₀⟫} := by
  classical
  have hμne : μ ≠ 0 := by
    intro hz
    simp [hz] at hx₀
  let fm : FiniteMeasure E := ⟨μ, inferInstance⟩
  have hfmne : fm ≠ 0 := by
    intro hz
    exact hμne (congrArg (fun η : FiniteMeasure E => (η : Measure E)) hz)
  have hmassne : fm.mass ≠ 0 := fm.mass_nonzero_iff.mpr hfmne
  have hmasspos : 0 < (fm.mass : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hmassne)
  let ν : ProbabilityMeasure E := fm.normalize
  have hnull (s : Set E) : (ν : Measure E) s = 0 ↔ μ s = 0 := by
    change (ν : Measure E) s = 0 ↔ (fm : Measure E) s = 0
    rw [← ν.ennreal_coeFn_eq_coeFn_toMeasure s,
      ← fm.ennreal_coeFn_eq_coeFn_toMeasure s]
    rw [ENNReal.coe_eq_zero, ENNReal.coe_eq_zero,
      fm.self_eq_mass_mul_normalize s, mul_eq_zero]
    simp [hmassne, ν]
  have hsupp : (ν : Measure E).support = μ.support := by
    ext x
    simp only [Measure.mem_support_iff_forall, pos_iff_ne_zero]
    exact forall_congr' fun s => forall_congr' fun _ => not_congr (hnull s)
  have hscale (s : Set E) : μ.real s = (fm.mass : ℝ) * (ν : Measure E).real s := by
    change (fm s : ℝ) = (fm.mass : ℝ) * (ν s : ℝ)
    exact_mod_cast fm.self_eq_mass_mul_normalize s
  have hν : x₀ ∈ interior (convexHull ℝ (ν : Measure E).support) := by
    rwa [hsupp]
  obtain ⟨m, hmpos, hmone, hhalf⟩ :=
    FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_readable ν hν
  refine ⟨(fm.mass : ℝ) * m, mul_pos hmasspos hmpos, ?_, ?_⟩
  · change (fm.mass : ℝ) * m ≤ (fm.mass : ℝ)
    exact mul_le_of_le_one_right hmasspos.le hmone
  · intro u hu
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hhalf u hu) hmasspos.le
