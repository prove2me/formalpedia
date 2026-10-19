-- Prove2me | solution 1 for BookProof.ChapterG3.qftVacuum_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T13:41:08.716441+00:00
-- url     : https://prove2.me/submissions/97a414f2-e361-4bb9-b316-a83cb4ccc27c

-- Generated from ChapterG3.lean — solution of BookProof.ChapterG3.qftVacuum_isProbability
import Mathlib
import Definitions.Def_ChapterG3
open BookProof.ChapterG3
open BookProof.ChapterG3.PhysHSGaussian



open MeasureTheory
open scoped ENNReal



variable {X : Type*}

variable {X : Type*}


/-! gaussianE_isProbability: inlined from `BookProof/PhysHSGaussian/Part1.lean`, because the
published `Def_ChapterG3` bundle carries only `gaussianE` itself. -/

open MeasureTheory Set Filter ProbabilityTheory

instance PhysHSGaussian.gaussianE_isProbability (k : ℕ) : IsProbabilityMeasure (gaussianE k) := by
  constructor ; norm_num [ gaussianE ];
  rw [ Measure.map_apply ] <;> norm_num;
  exact MeasurableEquiv.measurable _

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) : IsProbabilityMeasure (qftVacuum k) := PhysHSGaussian.gaussianE_isProbability k
