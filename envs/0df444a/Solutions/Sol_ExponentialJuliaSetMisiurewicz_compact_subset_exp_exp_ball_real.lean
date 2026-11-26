-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.compact_subset_exp_exp_ball_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:22.23981+00:00
-- url     : https://prove2.me/submissions/2d74d116-ca7e-41c4-931f-7c2b1560fde6

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_mem_exp_exp_ball_real

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {K : Set ℂ}
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ ρ : ℝ, ∀ x : ℝ, ρ ≤ x → K ⊆ expIterate 2 '' ball (x : ℂ) 8 := by
  have hcont : ContinuousOn (fun z : ℂ => |Real.log ‖z‖|) K := by
    apply ContinuousOn.abs
    apply ContinuousOn.log continuous_norm.continuousOn
    intro z hz
    exact norm_ne_zero_iff.mpr (fun h => hK0 (h ▸ hz))
  obtain ⟨M, hM⟩ := hK.bddAbove_image hcont
  refine ⟨M + 2 * Real.pi, fun x hx w hw => ?_⟩
  exact mem_exp_exp_ball_real (fun h => hK0 (h ▸ hw)) (hM ⟨w, hw, rfl⟩) hx
end ExponentialJuliaSetMisiurewicz
