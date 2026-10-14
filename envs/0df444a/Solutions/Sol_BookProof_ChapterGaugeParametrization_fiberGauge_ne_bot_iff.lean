-- Prove2me | solution 1 for BookProof.ChapterGaugeParametrization.fiberGauge_ne_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:54.396273+00:00
-- url     : https://prove2.me/submissions/84abae28-0479-4a87-8c24-57df571933df

-- Generated from ChapterGaugeParametrization.lean — solution of BookProof.ChapterGaugeParametrization.fiberGauge_ne_bot_iff
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
import Theorems.Thm_BookProof_ChapterGaugeParametrization_fiberGauge_eq_bot_iff
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeParametrization




open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

variable {X Y : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (π : X → Y) :
    fiberGauge π ≠ ⊥ ↔ ¬ Function.Injective π := by

  rw [Ne, fiberGauge_eq_bot_iff]
