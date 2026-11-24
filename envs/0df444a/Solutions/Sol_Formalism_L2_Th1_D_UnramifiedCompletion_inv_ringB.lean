-- Prove2me | solution 1 for Formalism.L2.Th1.D.UnramifiedCompletion.inv_ringB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:48.347725+00:00
-- url     : https://prove2.me/submissions/24c32df5-de07-40b4-8344-ef9a8c534016

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_ringA_le_ringB
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_geom_mem
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_inv_ringA
import Theorems.Thm_UpperTheory_Reformulated_B_Qi27_norm_ringA_le


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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)
open UnramifiedCompletion
open Formalism.L2.Th1.D.UnramifiedCompletion
variable {l : ℕ} [hl : Fact l.Prime]
namespace Formalism.L2.Th1.D.UnramifiedCompletion
theorem _root_.solution (hA : PerA l) {u : ℂ_[l]} (hu : u ∈ ringB l) (h : ‖u‖ = 1) : u⁻¹ ∈ ringB l := by
  obtain ⟨u0, hu0, hd⟩ :=
    Metric.mem_closure_iff.1 (show u ∈ closure (ringA l : Set ℂ_[l]) from hu) 1 one_pos
  rw [dist_eq_norm] at hd
  have hn : ‖u0‖ = 1 := by
    refine le_antisymm (norm_ringA_le hu0) ?_
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ‖u‖ ≤ max ‖u - u0‖ ‖u0‖ := by
      simpa using IsUltrametricDist.norm_add_le_max (u - u0) u0
    rw [h] at h1
    exact absurd h1 (not_le.2 (max_lt hd hlt))
  have hne : u0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  have hi := inv_ringA hA hu0 hn
  have hwB : u0⁻¹ * (u0 - u) ∈ ringB l := mul_mem hi (sub_mem (ringA_le_ringB hu0) hu)
  have hw : ‖u0⁻¹ * (u0 - u)‖ < 1 := by
    rw [norm_mul, norm_inv, hn, inv_one, one_mul, norm_sub_rev]; exact hd
  have e : u = u0 * (1 - u0⁻¹ * (u0 - u)) := by
    rw [mul_sub, mul_one, mul_inv_cancel_left₀ hne, sub_sub_cancel]
  have h5 := mul_mem hi (geom_mem hwB hw)
  rw [← mul_inv, ← e] at h5
  exact h5
end Formalism.L2.Th1.D.UnramifiedCompletion
