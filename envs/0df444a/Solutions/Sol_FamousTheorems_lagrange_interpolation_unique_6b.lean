-- Prove2me | solution 1 for FamousTheorems.lagrange_interpolation_unique_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:15:13.204697+00:00
-- url     : https://prove2.me/submissions/23830fcb-35e1-4c47-b8d0-d151ff74542a

import Mathlib

theorem solution {F ι : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} (r : ι → F) {f : Polynomial F}
    (hvs : Set.InjOn v s) (hf : f.degree < s.card) (heval : ∀ i ∈ s, f.eval (v i) = r i) :
    f = Lagrange.interpolate s v r :=
  Lagrange.eq_interpolate_of_eval_eq r hvs hf heval
