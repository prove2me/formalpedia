-- Prove2me | solution 1 for Formalism.GrowthSums.oddPowerInvSumIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:24.045011+00:00
-- url     : https://prove2.me/submissions/e619d23d-c68f-4fc8-857b-ef886a20c8f6

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
namespace Formalism.GrowthSums
theorem _root_.solution : GammaIdentity := by
  intro p hp
  have hp0 : p ≠ 0 := by positivity
  have hp2 : 1 < p ^ 2 := by nlinarith
  have hq : p ^ 2 - 1 ≠ 0 := by linarith
  have hq' : p - 1 ≠ 0 := by linarith
  have hr0 : (0 : ℝ) ≤ (p ^ 2)⁻¹ := by positivity
  have hr1 : (p ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp2
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).mul_left p⁻¹
  have hf : (fun n : ℕ => (p ^ (2 * n + 1))⁻¹) = fun i : ℕ => p⁻¹ * (p ^ 2)⁻¹ ^ i := by
    funext n
    rw [inv_pow, ← mul_inv]
    congr 1
    ring
  have hv : gamP p = p⁻¹ * (1 - (p ^ 2)⁻¹)⁻¹ := by
    unfold gamP rhoP
    have e : 1 - (p ^ 2)⁻¹ = (p ^ 2 - 1) / p ^ 2 := by field_simp
    rw [e, inv_div]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hf, hv]
    exact hs
  · unfold gamP rhoP
    field_simp
    ring
end Formalism.GrowthSums
