-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.trotterKato_tendstoUniformlyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T08:14:29.904357+00:00
-- url     : https://prove2.me/submissions/6fd794f6-89be-4834-b2bd-7d260980d479

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.trotterKato_tendstoUniformlyOn
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
theorem solution (hres : StrongResolventConvergence T S) (v : H)
    {T₀ : ℝ} (hT₀ : 0 ≤ T₀) :
    TendstoUniformlyOn (fun n t => (S n).stoneU t v) (fun t => T.stoneU t v) atTop
      (Set.Icc (-T₀) T₀) := by

  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h := trotterKato_uniform_on_interval T S hres v hT₀ (by positivity : (0:ℝ) < ε / 2)
  filter_upwards [h] with n hn t ht
  have habs : |t| ≤ T₀ := abs_le.mpr ⟨ht.1, ht.2⟩
  have := hn t habs
  rw [dist_eq_norm, norm_sub_rev]
  linarith
