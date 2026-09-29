-- Prove2me | solution 1 for FamousTheorems.zeckendorf
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T06:56:30.103269+00:00
-- url     : https://prove2.me/submissions/4e2f6423-ee35-40a2-906a-6d1f252e707a

import Mathlib

open Filter Set Topology

theorem solution : Nonempty (ℕ ≃ {l : List ℕ // l.IsZeckendorfRep}) :=
  ⟨Nat.zeckendorfEquiv⟩
