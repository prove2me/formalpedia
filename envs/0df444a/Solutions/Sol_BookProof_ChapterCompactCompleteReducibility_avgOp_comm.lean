-- Prove2me | solution 1 for BookProof.ChapterCompactCompleteReducibility.avgOp_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:39:53.775893+00:00
-- url     : https://prove2.me/submissions/50e1de6d-4742-44c8-ad20-3a045b56ac64

-- Generated from ChapterCompactCompleteReducibility.lean — solution of BookProof.ChapterCompactCompleteReducibility.avgOp_comm
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
import Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_integrable_conjOp
import Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_avgOp_apply
open BookProof.ChapterCompactCompleteReducibility




open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V))
    (T : V →L[ℂ] V) (h : G) (v : V) :
    avgOp μ ρ T (ρ h v) = ρ h (avgOp μ ρ T v) := by

  have hint : Integrable (fun g => ρ g (T ((ρ g).symm v))) μ := by
    have := (integrable_conjOp (μ := μ) hρ T).apply_continuousLinearMap v
    simpa [conjOp] using this
  rw [avgOp_apply hρ, avgOp_apply hρ]
  have hpull : ∫ g, ρ h (ρ g (T ((ρ g).symm v))) ∂μ = ρ h (∫ g, ρ g (T ((ρ g).symm v)) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm (ρ h : V →L[ℂ] V) hint
  rw [← hpull]
  have hshift := integral_mul_left_eq_self (μ := μ)
    (fun g : G => ρ g (T ((ρ g).symm (ρ h v)))) h
  rw [← hshift]
  have hmul : ∀ (a b : G) (x : V), ρ (a * b) x = ρ a (ρ b x) := by
    intro a b x
    rw [map_mul]
    rfl
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hkey : (ρ (h * k)).symm (ρ h v) = (ρ k).symm v := by
    have happ : ρ (h * k) ((ρ k).symm v) = ρ h v := by
      rw [hmul, (ρ k).apply_symm_apply]
    rw [← happ, (ρ (h * k)).symm_apply_apply]
  simp only [hkey, hmul]
