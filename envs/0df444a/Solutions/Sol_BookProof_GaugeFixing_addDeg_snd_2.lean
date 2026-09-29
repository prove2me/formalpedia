-- Prove2me | solution 2 for BookProof.GaugeFixing.addDeg_snd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:26:44.228514+00:00
-- url     : https://prove2.me/submissions/867712ce-e18e-450f-8fa0-cea2d782da0f

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.addDeg_snd
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing

set_option maxHeartbeats 1000000 in
theorem solution (a b : BiDegree) : (addDeg a b).2 = a.2 + b.2 := rfl
