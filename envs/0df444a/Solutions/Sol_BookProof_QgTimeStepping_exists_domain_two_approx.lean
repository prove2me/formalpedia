-- Prove2me | solution 1 for BookProof.QgTimeStepping.exists_domain_two_approx
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:09:36.403319+00:00
-- url     : https://prove2.me/submissions/5b9ac3cd-7557-4138-b06d-df9f4e83d2b9

-- Generated from ChapterQgTimeStepping.lean — theorem BookProof.QgTimeStepping.exists_domain_two_approx
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgTruncationResolvent
import Mathlib
import Definitions.Def_ChapterQgTimeStepping
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
open BookProof.QgTimeStepping



open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgOuterFockCoreFL BookProof.QgTruncationResolvent

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
open BookProof.QgTimeStepping in
theorem solution (v : H) {eps : ℝ} (heps : 0 < eps) :
    ∃ x : T.domain, T.op x ∈ T.domain ∧ ‖v - (x : H)‖ < eps := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (T.jn_tendsto v) eps heps
  set n : ℝ := (N : ℝ) + 1 with hn
  have hn0 : n ≠ 0 := by positivity
  have hn0' : -n ≠ 0 := neg_ne_zero.mpr hn0
  set y : T.domain := T.res (-n) v
  set z : T.domain := T.res n (y : H)
  refine ⟨((n : ℂ) ^ 2) • z, ?_, ?_⟩
  · rw [map_smul, T.op_res hn0 (y : H)]
    refine T.domain.smul_mem _ (T.domain.add_mem y.2 (T.domain.smul_mem _ z.2))
  · have h := hN N le_rfl
    rw [dist_comm, dist_eq_norm] at h
    have e : ((((n : ℂ) ^ 2) • z : T.domain) : H) = T.jn ((N : ℝ) + 1) v := by
      rw [T.jn_apply]; rfl
    rw [e]; exact h
