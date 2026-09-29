-- Prove2me | solution 1 for FamousTheorems.higman_lemma_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:48:55.393646+00:00
-- url     : https://prove2.me/submissions/6a32de35-b3ac-41a1-beaa-9cd5d3cdd1b8

import Mathlib

theorem solution {α : Type*} (r : α → α → Prop) [IsPreorder α r] {s : Set α} (hs : s.PartiallyWellOrderedOn r) :
    {l : List α | ∀ x ∈ l, x ∈ s}.PartiallyWellOrderedOn (List.SublistForall₂ r) :=
  hs.partiallyWellOrderedOn_sublistForall₂ r
