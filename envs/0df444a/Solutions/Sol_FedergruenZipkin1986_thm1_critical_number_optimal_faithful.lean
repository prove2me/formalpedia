-- Prove2me | solution 1 for FedergruenZipkin1986.thm1_critical_number_optimal_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:40:37.390217+00:00
-- url     : https://prove2.me/submissions/34cbadd3-d9db-45b9-ad6f-09a1b8e1c9bb

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model
import Theorems.Thm_FedergruenZipkin_AvgCost_theorem1_critical_number_optimal

open FedergruenZipkin.AvgCost

theorem solution (M : Model) (U yInf : ℤ)
    (hU0 : 0 < U)
    (hyInf : IsLeast {y : ℤ | ∀ z, M.G y ≤ M.G z} yInf) (hU : yInf ≤ U) :
    ∃ (g : ℝ) (v : ℤ → ℝ) (ystar : ℤ),
      (∀ y ≤ U, Summable (fun j : ℕ => M.p j * v (y - j))) ∧
      OptEq M U g v ∧
      ConvexBelow U v ∧
      ystar ≤ U ∧ yInf ≤ ystar ∧ (∀ x ≤ U, v ystar ≤ v x) ∧
      StronglyOptimal M U (critNum M ystar) g := by
  obtain ⟨g, v, ystar, h1, -, -, h2⟩ := theorem1_critical_number_optimal M U yInf hyInf hU
  exact ⟨g, v, ystar, h1, h2⟩
