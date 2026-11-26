-- Prove2me | solution 1 for EdenVerified.s06_global_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:52.652457+00:00
-- url     : https://prove2.me/submissions/7908877b-297d-4c00-9986-dc7489778520

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_globalGrowthDimension_eq_rate_ratio
import Theorems.Thm_Eden_globalGrowthDimension_eq_target
import Theorems.Thm_Eden_globalGrowthIndex_eq_four
import Theorems.Thm_Eden_globalGrowthInterpolation_integer
import Theorems.Thm_Eden_globalGrowthInterpolation_interpolate
import Theorems.Thm_Eden_globalGrowthInterpolation_isGreatest


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    (∀ k : ℕ, k ≤ 5 → globalGrowthInterpolation c k = globalGrowthRate c k) ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      globalGrowthInterpolation c ((k : ℝ)+α) =
        (1-α)*globalGrowthRate c k + α*globalGrowthRate c (k+1)) ∧
    kaplanYorkeIndex (globalGrowthIncrements c) = 4 ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d} (4+4/c) ∧
    globalGrowthDimension c = 4 + globalGrowthRate c 4 /
      (globalGrowthRate c 4 - globalGrowthRate c 5) ∧
    globalGrowthDimension c = 4+4/c :=
  ⟨fun k hk => globalGrowthInterpolation_integer hc.le hk,
    fun k hk α hα₀ hα₁ => globalGrowthInterpolation_interpolate hc.le hk hα₀ hα₁,
    globalGrowthIndex_eq_four hc, globalGrowthInterpolation_isGreatest hc,
    globalGrowthDimension_eq_rate_ratio hc, globalGrowthDimension_eq_target hc⟩
end EdenVerified
