-- Prove2me | solution 1 for FamousTheorems.two_colorable_iff_no_odd_cycle_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:03:47.176017+00:00
-- url     : https://prove2.me/submissions/9be32282-16f7-407f-bd4d-ec07ec9312e2

import Mathlib

theorem solution {α : Type*} {G : SimpleGraph α} : G.Colorable 2 ↔ ∀ (u : α) (w : G.Walk u u), Even w.length :=
  SimpleGraph.two_colorable_iff_forall_loop_even
