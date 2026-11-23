-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.exists_nhds_close
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:43.190365+00:00
-- url     : https://prove2.me/submissions/032b8256-f169-47b1-9f8a-0e347e884e71

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) (h1 : ∀ u, ρ 1 u = u)
    (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ V, ∀ y ∈ Y, ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖ := by
  let A : G → (Y →L[ℂ] H) := fun x => (ρ x).comp Y.subtypeL - Y.subtypeL
  have hA : Continuous A := by
    rw [continuous_clm_apply]
    intro y
    exact (hρ y).sub continuous_const
  have hA1 : A 1 = 0 := by
    ext y
    simp [A, h1]
  refine ⟨{x | ‖A x‖ < 1 / 2}, ?_, fun x hx y hy => ?_⟩
  · exact (isOpen_lt hA.norm continuous_const).mem_nhds (by simp [hA1])
  · have := (A x).le_opNorm ⟨y, hy⟩
    exact this.trans (mul_le_mul_of_nonneg_right (le_of_lt hx) (norm_nonneg _))
end CompanionTheory.D.gk.admitted.Gard
