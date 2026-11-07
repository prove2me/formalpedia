-- Prove2me | solution 1 for DaiWeissFluid.LuKumar.theorem5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:46:50.349273+00:00
-- url     : https://prove2.me/submissions/648ad7c1-517e-4ace-b296-7d6dfc539169

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network
import Theorems.Thm_DaiWeissFluid_LuKumar_wc_stable
import Theorems.Thm_DaiWeissFluid_LuKumar_priority_supersedes_wc
import Theorems.Thm_DaiWeissFluid_LuKumar_priority_unstable

open DaiWeissFluid.LuKumar

theorem solution (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1) :
    (¬ DaiWeissFluid.ThreeBuffer.FluidStable (luKumar m).IsWorkConserving ↔ 1 ≤ m 1 + m 3) ∧
    (¬ DaiWeissFluid.ThreeBuffer.FluidStable ((luKumar m).IsPrioritySolution piLK) ↔ 1 ≤ m 1 + m 3) := by
  have hsub : DaiWeissFluid.ThreeBuffer.FluidStable (luKumar m).IsWorkConserving →
      DaiWeissFluid.ThreeBuffer.FluidStable ((luKumar m).IsPrioritySolution piLK) := by
    rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun Q T hP => h Q T (priority_supersedes_wc (luKumar m) hm piLK Q T hP)⟩
  refine ⟨⟨fun h => ?_, fun h hs => priority_unstable m hm h51₁ h51₂ h (hsub hs)⟩,
    ⟨fun h => ?_, fun h => priority_unstable m hm h51₁ h51₂ h⟩⟩
  · by_contra hc
    exact h (wc_stable m hm h51₁ h51₂ (lt_of_not_ge hc))
  · by_contra hc
    exact h (hsub (wc_stable m hm h51₁ h51₂ (lt_of_not_ge hc)))
