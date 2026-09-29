-- Prove2me | solution 1 for FamousTheorems.szpilrajn
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:10:24.600391+00:00
-- url     : https://prove2.me/submissions/ef0d237c-4a4b-4d3b-b618-237d676d657a

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {α : Type*} (r : α → α → Prop) [IsPartialOrder α r] :
    ∃ s : α → α → Prop, IsLinearOrder α s ∧ r ≤ s := extend_partialOrder r
