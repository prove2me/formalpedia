-- Prove2me | solution 2 for BookProof.GaugeFixing.addDeg_fst
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:25:24.569961+00:00
-- url     : https://prove2.me/submissions/e8201b77-a387-4d7f-a810-8abf2f52936f

-- Generated from ChapterGaugeFixing.lean — solution of BookProof.GaugeFixing.addDeg_fst
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing

set_option maxHeartbeats 1000000 in
theorem solution (a b : BiDegree) : (addDeg a b).1 = a.1 + b.1 := rfl
