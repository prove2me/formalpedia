-- Prove2me | solution 1 for BookProof.GaugeFixing.addDeg_fst
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:45:36.452707+00:00
-- url     : https://prove2.me/submissions/e52269b1-a040-4f87-a659-b86a42026faa

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.addDeg_fst
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing

theorem solution (a b : BiDegree) : (addDeg a b).1 = a.1 + b.1 := rfl
