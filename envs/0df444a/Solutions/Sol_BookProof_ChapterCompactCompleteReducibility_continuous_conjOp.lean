-- Prove2me | solution 1 for BookProof.ChapterCompactCompleteReducibility.continuous_conjOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:39:12.461468+00:00
-- url     : https://prove2.me/submissions/0535b9f4-05ff-474e-a503-dfa69df50505

-- Generated from ChapterCompactCompleteReducibility.lean — solution of BookProof.ChapterCompactCompleteReducibility.continuous_conjOp
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
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
omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [FiniteDimensional ℂ V] in
theorem solution {ρ : G →* (V ≃L[ℂ] V)}
    (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) :
    Continuous (conjOp ρ T) := by

  have hinv : Continuous fun g : G => ((ρ g).symm : V →L[ℂ] V) := by
    have : (fun g : G => ((ρ g).symm : V →L[ℂ] V)) = fun g : G => ((ρ g⁻¹ : V ≃L[ℂ] V) :
        V →L[ℂ] V) := by
      funext g
      congr 1
      rw [map_inv]
      rfl
    rw [this]
    exact hρ.comp continuous_inv
  exact hρ.clm_comp (continuous_const.clm_comp hinv)
