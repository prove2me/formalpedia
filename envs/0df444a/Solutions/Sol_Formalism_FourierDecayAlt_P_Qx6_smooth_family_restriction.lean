-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.smooth_family_restriction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:40:07.7168+00:00
-- url     : https://prove2.me/submissions/ff3fdff5-65ef-456a-86cd-28cf87c9dad1

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_cd_mL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_mul_mem_of_mem_inv_mul_ideal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_isOpen_OmXX


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hW : WeylLevelElementFacts) (l : Fin r) {U U' : Set (XX k r)} {Φ : Fn k r E}
    (h : SmoothFam k r l.castSucc U Φ) (hU' : ∀ x ∈ U', x.1 ∈ OmX r ∧ mL k r l x ∈ U) :
    SmoothFam k r l.succ U' (fun c g => Φ c (w1 k r l (c l) * g)) := by
  intro x₀ hx₀ hg₀
  obtain ⟨hc₀, hm₀⟩ := hU' x₀ hx₀
  obtain ⟨V, F, hV, hxV, hF, hΦ⟩ := h (mL k r l x₀) hm₀ (mul_mem_of_mem_inv_mul_ideal hW l (hc₀ l) hg₀)
  refine ⟨{x : XX k r | x.1 ∈ OmX r} ∩ mL k r l ⁻¹' V, fun x => F (mL k r l x),
    (cd_mL (k := k) l).continuousOn.isOpen_inter_preimage Qx3.isOpen_OmXX hV, ⟨hc₀, hxV⟩, ?_, ?_⟩
  · exact hF.comp ((cd_mL l).mono Set.inter_subset_left) (fun x hx => hx.2)
  · intro x hx hxG
    exact hΦ (mL k r l x) hx.2 (mul_mem_of_mem_inv_mul_ideal hW l (hx.1 l) hxG)
end Formalism.FourierDecayAlt.P.Qx6
