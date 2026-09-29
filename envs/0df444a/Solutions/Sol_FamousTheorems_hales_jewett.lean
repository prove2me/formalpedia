-- Prove2me | solution 1 for FamousTheorems.hales_jewett
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:49:26.667186+00:00
-- url     : https://prove2.me/submissions/25f7a989-4ac8-452d-923b-f5f65ef2fbab

import Mathlib

theorem solution (α : Type*) [Finite α] (κ : Type*) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Combinatorics.Line α ι, Combinatorics.Line.IsMono C l :=
  Combinatorics.Line.exists_mono_in_high_dimension α κ
