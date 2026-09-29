-- Prove2me | solution 1 for FamousTheorems.pow_card_sub_one_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T01:51:32.937013+00:00
-- url     : https://prove2.me/submissions/cb4921b6-d927-4c4f-ba82-b1014c570693

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem solution {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
