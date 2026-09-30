-- Prove2me | solution 1 for FriedbergMuchnik.recursive_projection_re
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T20:04:34.268379+00:00
-- url     : https://prove2.me/submissions/636a609a-8663-4721-b440-dd4cec730c8c

import Mathlib.Computability.RE

set_option backward.isDefEq.respectTransparency false

theorem solution (R : ℕ → ℕ → Prop)
    (hR : ComputablePred (fun p : ℕ × ℕ => R p.1 p.2)) :
    REPred (fun n => ∃ s, R n s) := by
  classical
  have hc : Computable (fun p : ℕ × ℕ => decide (R p.1 p.2)) := hR.decide
  have hp : Partrec (fun n => Nat.rfind (fun s => Part.some (decide (R n s)))) :=
    Partrec.rfind hc.partrec
  exact hp.dom_re.of_eq (fun n => by simp [Nat.rfind_dom])
