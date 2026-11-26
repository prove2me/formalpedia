-- Prove2me | solution 1 for EdenVerified.periodic_global_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:11.389643+00:00
-- url     : https://prove2.me/submissions/491833fd-cc04-46ab-82e8-da8448c9cb32

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_interpolate
import Theorems.Thm_Eden_periodicGlobalGrowthRate_eq
import Theorems.Thm_Eden_periodicGlobalGrowthRate_table
import Theorems.Thm_Eden_periodicGlobalLogGrowth_eq
import Theorems.Thm_Eden_tendsto_periodicGlobalLogGrowth_div


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    (∀ k : Fin 6, ∀ t : ℝ, 0 ≤ t →
      periodicGlobalLogGrowth c k t = t * (![0, 2, 2, 0, -2, -2 - c] : Fin 6 → ℝ) k) ∧
    (∀ k : Fin 6, Tendsto (fun t : ℝ => periodicGlobalLogGrowth c k t / t)
      atTop (𝓝 ((![0, 2, 2, 0, -2, -2 - c] : Fin 6 → ℝ) k))) ∧
    ((fun k : Fin 6 => periodicGlobalGrowthRate c k) = ![0, 2, 2, 0, -2, -2 - c]) ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      periodicGlobalGrowthInterpolation c ((k : ℝ) + α) =
        (1 - α) * periodicGlobalGrowthRate c k + α * periodicGlobalGrowthRate c (k + 1)) := by
  have hrate (k : Fin 6) := congrFun (periodicGlobalGrowthRate_table hc) k
  refine ⟨?_, ?_, periodicGlobalGrowthRate_table hc, ?_⟩
  · intro k t ht
    rw [periodicGlobalLogGrowth_eq hc ht (by omega),
      ← periodicGlobalGrowthRate_eq hc (by omega), hrate k]
  · intro k
    have h := tendsto_periodicGlobalLogGrowth_div hc (k := k) (by omega)
    rw [← periodicGlobalGrowthRate_eq hc (by omega), hrate k] at h
    exact h
  · exact fun k hk α hα₀ hα₁ => periodicGlobalGrowthInterpolation_interpolate hc hk hα₀ hα₁
end EdenVerified
