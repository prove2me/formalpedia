-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.isPhysicalObservable_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:26:29.156573+00:00
-- url     : https://prove2.me/submissions/4dd3792e-78e7-4d52-a282-894dda6ae30d

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.isPhysicalObservable_of_tendsto
import Mathlib
import Definitions.Def_ChapterGaugeCasimirAverage
open BookProof.ChapterGaugeCasimirAverage




open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]
variable {X : Type*}
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → X → ℝ} (hf : ∀ i, IsPhysicalObservable G (f i)) {F : X → ℝ}
    (h : ∀ x, Filter.Tendsto (fun i => f i x) l (nhds (F x))) :
    IsPhysicalObservable G F := by

  intro g x
  have hx : Filter.Tendsto (fun i => f i (g • x)) l (nhds (F x)) := by
    have heq : (fun i => f i (g • x)) = fun i => f i x := funext fun i => hf i g x
    rw [heq]
    exact h x
  exact tendsto_nhds_unique (h (g • x)) hx
