-- Prove2me | solution 1 for BookProof.GaugeFixing.addDeg_snd
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:45:33.827936+00:00
-- url     : https://prove2.me/submissions/5521f72a-6e87-4a50-9eaf-9612fc0539c0

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.addDeg_snd
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing

theorem solution (a b : BiDegree) : (addDeg a b).2 = a.2 + b.2 := rfl
