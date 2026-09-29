-- Prove2me | solution 1 for FamousTheorems.compact_iff_totally_bounded_complete_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:58:11.834659+00:00
-- url     : https://prove2.me/submissions/3a3975c2-69ce-4aec-a327-3309bfc36467

import Mathlib

theorem solution {α : Type*} [UniformSpace α] {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s :=
  isCompact_iff_totallyBounded_isComplete
