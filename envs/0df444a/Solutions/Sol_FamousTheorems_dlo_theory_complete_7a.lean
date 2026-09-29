-- Prove2me | solution 1 for FamousTheorems.dlo_theory_complete_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:53:03.736571+00:00
-- url     : https://prove2.me/submissions/9ba01ffe-d9d0-4bfd-8938-b175a42200f8

import Mathlib

theorem solution : FirstOrder.Language.order.dlo.IsComplete :=
  FirstOrder.Language.dlo_isComplete
