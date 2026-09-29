-- Prove2me | solution 1 for FamousTheorems.covering_map_path_lifting_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:50:21.676746+00:00
-- url     : https://prove2.me/submissions/fe5f5921-f5ec-4315-a368-14cc8423e661

import Mathlib

theorem solution {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} (hp : IsCoveringMap p)
    (γ : C(unitInterval, X)) (e : E) (he : γ 0 = p e) :
    ∃ Γ : C(unitInterval, E), p ∘ Γ = γ ∧ Γ 0 = e :=
  hp.exists_path_lifts γ e he
