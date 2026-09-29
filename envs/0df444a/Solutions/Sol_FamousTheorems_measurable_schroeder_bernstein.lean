-- Prove2me | solution 1 for FamousTheorems.measurable_schroeder_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:10:25.101531+00:00
-- url     : https://prove2.me/submissions/9f5f31ec-c3b6-4420-bf01-1b9bd72aa5b5

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} {g : β → α} (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g) :
    Nonempty (α ≃ᵐ β) := ⟨hf.schroederBernstein hg⟩
