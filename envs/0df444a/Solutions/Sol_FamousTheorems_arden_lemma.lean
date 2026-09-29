-- Prove2me | solution 1 for FamousTheorems.arden_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T21:54:14.833554+00:00
-- url     : https://prove2.me/submissions/66cf4729-3b3d-49a8-a9cb-f531bd93a8f5

import Mathlib

theorem solution {α : Type*} {l m n : Language α} (hm : [] ∉ m) : l = m * l + n ↔ l = KStar.kstar m * n := by
  exact Language.self_eq_mul_add_iff hm
