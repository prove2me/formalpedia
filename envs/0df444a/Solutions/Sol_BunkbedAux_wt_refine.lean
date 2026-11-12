-- Prove2me | solution 1 for BunkbedAux.wt_refine
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T01:04:31.434478+00:00
-- url     : https://prove2.me/submissions/c1fbd251-f517-4550-be58-56181236599c

import Definitions.Def_BunkbedWZRefined

open Bunkbed.Hyper Bunkbed.Hyper.WZExt

theorem solution (P : WZ → ℚ) :
    wt P (Sum.inr 0) + wt P (Sum.inr 1) = P WZ.abc * P WZ.a_b_c ∧
    wt P (Sum.inr 2) + wt P (Sum.inr 3) = P WZ.a_b_c * P WZ.abc ∧
    (∀ q : WZExt, toPair (rho q) = ((toPair q).2, (toPair q).1)) ∧
    (∀ q : WZExt, wt P (rho q) = wt P q) := by
  refine ⟨by simp only [wt]; ring, by simp only [wt]; ring, by decide, ?_⟩
  intro q
  rcases q with ⟨a, b⟩ | i
  · cases a <;> cases b <;> simp only [wt, rho] <;> ring
  · fin_cases i <;> simp only [wt, rho] <;> ring
