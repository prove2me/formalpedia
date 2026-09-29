-- Prove2me | solution 1 for FamousTheorems.prenex_normal_form_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:52:12.063977+00:00
-- url     : https://prove2.me/submissions/933be43e-50c8-4076-8b03-a40259acd4e0

import Mathlib

theorem solution {L : FirstOrder.Language} {M : Type*} [L.Structure M] {α : Type*} {n : ℕ} [Nonempty M]
    (φ : L.BoundedFormula α n) {v : α → M} {xs : Fin n → M} :
    φ.toPrenex.IsPrenex ∧ (φ.toPrenex.Realize v xs ↔ φ.Realize v xs) :=
  ⟨φ.toPrenex_isPrenex, φ.realize_toPrenex⟩
