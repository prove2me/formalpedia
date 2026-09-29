-- Prove2me | solution 1 for FamousTheorems.free_group_reduction_church_rosser
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:38:58.836681+00:00
-- url     : https://prove2.me/submissions/97c38327-9220-4840-bd1e-82597567530a

import Mathlib

theorem solution {α : Type*} {L₁ L₂ L₃ : List (α × Bool)} (h₁₂ : FreeGroup.Red L₁ L₂) (h₁₃ : FreeGroup.Red L₁ L₃) :
    Relation.Join FreeGroup.Red L₂ L₃ :=
  FreeGroup.Red.church_rosser h₁₂ h₁₃
