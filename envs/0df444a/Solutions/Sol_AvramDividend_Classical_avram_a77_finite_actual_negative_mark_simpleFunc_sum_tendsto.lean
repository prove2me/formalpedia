-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_finite_actual_negative_mark_simpleFunc_sum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:52:38.195126+00:00
-- url     : https://prove2.me/submissions/4e17ff1e-3437-4cdc-bc6c-d33297808ca0

/- Any finite original physical negative jump-time set admits
   finite-sum passage from pointwise quantisers to signed source sum. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    (S : Finset ℝ≥0) (mark : ℝ≥0 → ℝ) (θ : ℝ)
    (hNeg : ∀ u ∈ S, mark u < 0)
    (q : ℕ → SimpleFunc ℝ ℝ)
    (hPoint : ∀ y, y < 0 →
      Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) :
    Tendsto (fun n => ∑ u ∈ S, q n (mark u))
      atTop (𝓝 (θ * ∑ u ∈ S, mark u)) := by
  have hs : Tendsto (fun n => ∑ u ∈ S, q n (mark u))
      atTop (𝓝 (∑ u ∈ S, θ * mark u)) :=
    tendsto_finsetSum S (fun u hu => hPoint (mark u) (hNeg u hu))
  simpa only [Finset.mul_sum] using hs

