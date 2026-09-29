-- Prove2me | solution 1 for FamousTheorems.dershowitz_manna_well_founded
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:16:52.14469+00:00
-- url     : https://prove2.me/submissions/cd1c17a7-2e75-41fb-b5d3-8b6809a9bd5f

import Mathlib

theorem solution {α : Type*} [Preorder α] [WellFoundedLT α] :
    WellFounded (Multiset.IsDershowitzMannaLT : Multiset α → Multiset α → Prop) :=
  Multiset.wellFounded_isDershowitzMannaLT
