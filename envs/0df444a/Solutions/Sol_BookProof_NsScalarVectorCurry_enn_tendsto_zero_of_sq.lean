-- Prove2me | solution 1 for BookProof.NsScalarVectorCurry.enn_tendsto_zero_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:19.250522+00:00
-- url     : https://prove2.me/submissions/3ee2f70f-11e3-4a1d-b032-5863306578e6

-- Generated from ChapterNsScalarVectorCurry.lean — solution of BookProof.NsScalarVectorCurry.enn_tendsto_zero_of_sq
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry



open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}
variable [SigmaFinite μ] [SigmaFinite ν]

set_option maxHeartbeats 1000000 in
theorem solution {u : ℕ → ℝ≥0∞}
    (h : Filter.Tendsto (fun k => u k ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by

  rw [ENNReal.tendsto_nhds_zero] at h ⊢
  intro ε hε
  filter_upwards [h (ε ^ 2) (by positivity)] with k hk
  by_contra hlt
  push_neg at hlt
  exact absurd hk (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero hlt))
