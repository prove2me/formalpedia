-- Prove2me | solution 1 for FamousTheorems.schroeder_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:10:47.984879+00:00
-- url     : https://prove2.me/submissions/b0ff6d80-2670-4351-8098-a7dd544dd3ec

import Mathlib

theorem solution : ∀ {α β : Type*} {f : α → β} {g : β → α}, Function.Injective f →
    Function.Injective g → ∃ h : α → β, Function.Bijective h :=
  Function.Embedding.schroeder_bernstein
