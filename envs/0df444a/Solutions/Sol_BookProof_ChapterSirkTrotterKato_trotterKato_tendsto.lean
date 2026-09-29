-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.trotterKato_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T08:13:09.453595+00:00
-- url     : https://prove2.me/submissions/04f3b7fd-8998-4353-8fc5-0d4621bd4dbd

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.trotterKato_tendsto
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_uniform_on_interval
open BookProof.ChapterSirkTrotterKato











noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution (hres : StrongResolventConvergence T S) (v : H) (t : ℝ) :
    Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by

  rw [Metric.tendsto_atTop]
  intro ε hε
  have h := trotterKato_uniform_on_interval T S hres v (abs_nonneg t)
    (by positivity : (0:ℝ) < ε / 2)
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn t le_rfl
  rw [dist_eq_norm]
  linarith
