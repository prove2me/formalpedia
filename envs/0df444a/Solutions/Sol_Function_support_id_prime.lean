-- Prove2me | solution 1 for Function.support_id_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:03:44.447285+00:00
-- url     : https://prove2.me/submissions/eccf6e90-d227-4233-90a8-9a037207511c

import Mathlib.Algebra.Notation.Support

open Function

variable {α : Type*} [Zero α]

theorem Function.support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

open Function in
theorem solution {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id
