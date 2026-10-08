-- Prove2me | solution 1 for FiniteMagmaE677.idempotent_e255
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:20:10.471369+00:00
-- url     : https://prove2.me/submissions/28f0f073-fc40-4907-b4d9-a1dda3a7bf18

import Definitions.Def_FiniteMagmaE677

/-!
# Idempotent elements satisfy equation 255

If `x ⋄ x = x`, then equation 255 holds at `x`: with `(x ⋄ x) = x` the
expression `((x ⋄ x) ⋄ x) ⋄ x` collapses to `x ⋄ x = x`. No E677 hypothesis,
no finiteness, and no left-cancellation is needed.

Combined with the orbit-period theorems (periods two and three are
impossible, so non-idempotent elements of a finite E677 magma have left
orbit of length at least four), this localizes any failure of 255 to
elements with long orbits.
-/

universe u

theorem FiniteMagmaE677.idempotent_e255 {α : Type u}
    (op : α → α → α) (x : α) (hid : op x x = x) :
    x = op (op (op x x) x) x := by
  rw [hid, hid, hid]

theorem solution {α : Type u}
    (op : α → α → α) (x : α) (hid : op x x = x) :
    x = op (op (op x x) x) x :=
  FiniteMagmaE677.idempotent_e255 op x hid
