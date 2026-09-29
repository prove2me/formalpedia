-- Prove2me | solution 1 for FamousTheorems.infinite_pigeonhole_principle_cardinal
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:16:53.837722+00:00
-- url     : https://prove2.me/submissions/3b96503f-3dea-4db7-8b92-25c8ba0abaed

import Mathlib

universe u

theorem solution {α β : Type u} (f : β → α) (hβ : Cardinal.aleph0 ≤ Cardinal.mk β)
    (hα : Cardinal.mk α < (Cardinal.mk β).ord.cof) :
    ∃ a : α, Cardinal.mk (f ⁻¹' {a}) = Cardinal.mk β :=
  Cardinal.infinite_pigeonhole f hβ hα
