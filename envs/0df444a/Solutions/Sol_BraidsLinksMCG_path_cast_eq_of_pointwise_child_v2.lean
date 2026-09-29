-- Prove2me | solution 1 for BraidsLinksMCG.path_cast_eq_of_pointwise_child_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T16:31:49.618343+00:00
-- url     : https://prove2.me/submissions/1e5f4f3d-558b-47ef-a752-5cbfc50e810b

import Mathlib

theorem solution {X : Type*} [TopologicalSpace X] {a b c d : X}
    (p : Path a b) (q : Path c d) (hc : c = a) (hd : d = b)
    (h : ∀ t, p t = q t) : p.cast hc hd = q := by
  ext t
  exact h t
