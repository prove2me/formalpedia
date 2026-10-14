-- Prove2me | solution 1 for BookProof.ChapterGaugeParametrization.apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:35.634993+00:00
-- url     : https://prove2.me/submissions/4100041f-8521-4a48-ab12-4be9dff9b3ea

-- Generated from ChapterGaugeParametrization.lean — solution of BookProof.ChapterGaugeParametrization.apply_eq
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeParametrization




open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

variable {X Y : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (π : X → Y) (σ : fiberGauge π) (x : X) : π (σ • x) = π x := σ.property x
