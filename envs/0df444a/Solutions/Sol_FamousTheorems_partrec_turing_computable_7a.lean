-- Prove2me | solution 1 for FamousTheorems.partrec_turing_computable_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:54:08.220971+00:00
-- url     : https://prove2.me/submissions/000bd7cc-4f66-4870-a5ba-d59b29520cad

import Mathlib

theorem solution (c : Turing.ToPartrec.Code) (v : List ℕ) :
    StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr) (Turing.PartrecToTM2.init c v) =
      Turing.PartrecToTM2.halt <$> c.eval v :=
  Turing.PartrecToTM2.tr_eval c v
