-- Prove2me | solution 1 for FamousTheorems.post_computable_iff_re_and_co_re
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:07:39.480398+00:00
-- url     : https://prove2.me/submissions/ba6ff340-52f1-49ca-aa13-62976557e348

import Mathlib

theorem solution {α : Type*} [Primcodable α] {p : α → Prop} [DecidablePred p] :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a :=
  ComputablePred.computable_iff_re_compl_re
