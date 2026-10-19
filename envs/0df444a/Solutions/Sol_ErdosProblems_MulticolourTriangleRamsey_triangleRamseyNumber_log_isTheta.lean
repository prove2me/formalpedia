-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_isTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/3af1eddc-48f2-4735-8673-52b408823899

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_log_eventually_bounds

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution :
    (fun k : ℕ => Real.log (triangleRamseyNumber k : ℝ))
      =Θ[atTop] (fun k : ℕ => (k : ℝ) * Real.log (k : ℝ)) := by
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨2, ?_⟩
    filter_upwards [triangleRamseyNumber_log_eventually_bounds,
      eventually_ge_atTop 4] with k hbounds hk
    have hscale : 0 ≤ (k : ℝ) * Real.log (k : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
    have hlog : 0 ≤ Real.log (triangleRamseyNumber k : ℝ) := by
      nlinarith [hbounds.1]
    change |Real.log (triangleRamseyNumber k : ℝ)| ≤
      (2 : ℝ) * |(k : ℝ) * Real.log (k : ℝ)|
    rw [abs_of_nonneg hlog, abs_of_nonneg hscale]
    simpa [mul_assoc] using hbounds.2
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨6, ?_⟩
    filter_upwards [triangleRamseyNumber_log_eventually_bounds,
      eventually_ge_atTop 4] with k hbounds hk
    have hscale : 0 ≤ (k : ℝ) * Real.log (k : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
    have hlog : 0 ≤ Real.log (triangleRamseyNumber k : ℝ) := by
      nlinarith [hbounds.1]
    have hreverse :
        (k : ℝ) * Real.log (k : ℝ) ≤
          6 * Real.log (triangleRamseyNumber k : ℝ) := by
      nlinarith [hbounds.1]
    change |(k : ℝ) * Real.log (k : ℝ)| ≤
      (6 : ℝ) * |Real.log (triangleRamseyNumber k : ℝ)|
    rw [abs_of_nonneg hscale, abs_of_nonneg hlog]
    exact hreverse
end ErdosProblems.MulticolourTriangleRamsey
