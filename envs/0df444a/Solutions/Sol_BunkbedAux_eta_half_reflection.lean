-- Prove2me | solution 1 for BunkbedAux.eta_half_reflection
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T01:04:30.919175+00:00
-- url     : https://prove2.me/submissions/39d8377e-acbf-4118-b06d-56d97f22f6e7

import Definitions.Def_BunkbedWZRefined

open Bunkbed.Hyper Bunkbed.Hyper.WZExt

theorem solution (P : WZ → ℚ) :
    (∀ q : WZExt, inLamSq q = true → eta (eta q) = q) ∧
    (∀ q : WZExt, inLamSq q = true → inLamSq (eta q) = true) ∧
    (∀ q : WZExt, inLamSq q = true → wt P (eta q) = wt P q) ∧
    (∀ q : WZExt, inLamSq q = true → eta (rho q) = rho (eta q)) ∧
    (∀ q : WZExt, inLamSq q = true → (toPair q).1 = WZ.abc →
       ((toPair (eta q)).1 = WZ.abc ∨ (toPair (eta q)).1 = WZ.ab_c) ∧
       ((toPair (eta q)).2 = WZ.abc ∨ (toPair (eta q)).2 = WZ.ac_b)) ∧
    (∀ q : WZExt, inLamSq q = true →
       ((toPair q).1 = WZ.abc ∨ (toPair q).1 = WZ.ab_c) →
       ((toPair (eta q)).1 = WZ.abc ∨ (toPair (eta q)).1 = WZ.ab_c)) ∧
    (∀ q : WZExt, inLamSq q = true →
       ((toPair q).1 = WZ.abc ∨ (toPair q).1 = WZ.ac_b) →
       ((toPair (eta q)).2 = WZ.abc ∨ (toPair (eta q)).2 = WZ.ac_b)) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide⟩
  intro q hq
  rcases q with ⟨a, b⟩ | i
  · cases a <;> cases b <;> simp_all [wt, eta, inLamSq] <;> ring
  · fin_cases i <;> simp_all [wt, eta, inLamSq] <;> ring
