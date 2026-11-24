-- Prove2me | solution 1 for Formalism.L2.Th1.D.KurIntegers_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:59:09.555909+00:00
-- url     : https://prove2.me/submissions/4f1d9a69-2355-4838-92d3-c707fc3715dc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_ringA_le_ringB
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_isClosed_ringB
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_div_ringB
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_inv_ringB
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_mem_of_pow_mul
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_ringB_le_Kur

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
namespace Formalism.L2.Th1.D
theorem _root_.solution : RingAFacts → KurIntegers := by
  intro hA l hl
  have hA2 : PerA l := (hA l).2
  have hdiv : DivB l := fun x hx h => div_ringB hA2 hx h
  have hinv : ∀ x ∈ ringB l, ‖x‖ = 1 → x⁻¹ ∈ ringB l := fun x hx h => inv_ringB hA2 hx h
  refine ⟨fun x => ⟨fun hx => ⟨ringB_le_Kur hx, norm_ringB_le hx⟩, ?_⟩, hdiv, hinv⟩
  rintro ⟨hK, h1⟩
  have hF : Subfield.closure (muPrime l) ≤ fracS hdiv hinv :=
    Subfield.closure_le.2 fun z hz =>
      ⟨0, by simpa using ringA_le_ringB (Subring.subset_closure hz)⟩
  have h2 : x ∈ closure (ringB l : Set ℂ_[l]) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨x0, hx0, hd⟩ := Metric.mem_closure_iff.1
      (show x ∈ closure ((Subfield.closure (muPrime l) : Subfield ℂ_[l]) : Set ℂ_[l]) from hK)
      (min ε 1) (lt_min hε one_pos)
    refine ⟨x0, ?_, hd.trans_le (min_le_left _ _)⟩
    obtain ⟨k, hk⟩ := hF hx0
    have hn : ‖x0‖ ≤ 1 := by
      have h3 : ‖x0‖ ≤ max ‖x0 - x‖ ‖x‖ := by
        simpa using IsUltrametricDist.norm_add_le_max (x0 - x) x
      refine h3.trans (max_le ?_ h1)
      rw [← dist_eq_norm, dist_comm]
      exact (hd.trans_le (min_le_right _ _)).le
    exact mem_of_pow_mul hdiv k x0 hn hk
  rwa [isClosed_ringB.closure_eq] at h2
end Formalism.L2.Th1.D
