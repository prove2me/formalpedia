-- Prove2me | solution 1 for FamousTheorems.hydra_cut_expand_well_founded_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:14:35.904379+00:00
-- url     : https://prove2.me/submissions/19a987c5-d234-4190-bc17-eb7094125db6

import Mathlib

theorem solution {α : Type*} {r : α → α → Prop} (hr : WellFounded r) : WellFounded (Relation.CutExpand r) :=
  hr.cutExpand
