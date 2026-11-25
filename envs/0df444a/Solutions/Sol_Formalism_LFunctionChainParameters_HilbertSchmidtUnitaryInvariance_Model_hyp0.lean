-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model.hyp0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:26.158264+00:00
-- url     : https://prove2.me/submissions/5823834a-4b4f-4858-a0c0-caa6d5f3171f

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Model_frame0
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Model_hs_one
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Model_kp0
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Model_en_isom
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Model_model_rank_one_or_two
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Model_model_unitary
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Model_model_unitary_entries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
open Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model
theorem _root_.solution :
    ChainHyp (d := fun _ => 2) (r := r0) P0 (fun u => En (r0 u)) (fun _ => 1) c0 V0 U0 J0 modelEmbedding A0 1
      (fun _ => 1) 2 (1 / 20) 0 0 0 (1 / 40) (1 / 2) 1 1 := by
  refine ⟨fun _ => by norm_num, by norm_num, by norm_num, le_refl _, by norm_num, by norm_num, ?_,
      fun _ => by norm_num, by norm_num, by norm_num, by norm_num, le_refl _,
      by rw [Real.sqrt_zero]; norm_num, ?_, ?_,
      by norm_num, by norm_num, ?_, ?_, model_unitary, model_unitary_entries, frame0, by norm_num, by norm_num, by simp,
      fun _ => by simp, fun u => by simp [A0]⟩
  · have : (1 : ℝ) * 1 ^ 2 / (1 / 20) = ((20 : ℕ) : ℝ) := by norm_num
    rw [this, Nat.ceil_natCast]; simp
  · refine ⟨fun u u' _ => ?_, fun u => ?_, by norm_num⟩
    · rw [kp0, hs_one]; norm_num
    · have : Kd (d := fun _ => 2) P0 (fun _ => (1 : ℝ)) u = 1 := kp0 u u
      rw [this]; simp [hsSq]
  · intro u; exact en_isom _ (model_rank_one_or_two u)
  · have h : ∀ u : Fin 20, (((2 : ℕ) : ℝ) - (r0 u : ℝ)) = if u = 0 then 1 else 0 := by
      intro u; unfold r0; split_ifs <;> norm_num
    simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [Rs]; norm_num
  · intro u; simp [c0]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model
