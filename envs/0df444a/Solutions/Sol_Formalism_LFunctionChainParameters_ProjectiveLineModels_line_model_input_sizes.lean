-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.line_model_input_sizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:58.021874+00:00
-- url     : https://prove2.me/submissions/5c5db8c6-47b2-400d-a659-3068f0c684a6

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_distinct_lines_gram_hs_le_one
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_matrix_gram_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ProjectiveLineModels
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates
variable (p : ℕ) [Fact p.Prime]
namespace Formalism.LFunctionChainParameters.ProjectiveLineModels
theorem _root_.solution :
    InputSG (I := Option (ZMod p) × ZMod p) (ι := fun _ => ZMod p) (lineMat p) (fun _ => 1)
      ((p : ℝ) ^ 2) 0 0 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨fun i j hij => ?_, fun i => ?_, ?_⟩
  · have := distinct_lines_gram_hs_le_one p i j hij
    simp only [KpG, mul_one, Real.sqrt_one, Complex.ofReal_one, one_smul, ZMod.card]
    have e : (1 + 0) * (p : ℝ) * (p : ℝ) / (p : ℝ) ^ 2 = 1 := by
      rw [add_zero, one_mul, sq]
      exact div_self (by positivity)
    rw [e]
    exact this
  · simp [KdG, KpG, line_matrix_gram_self, hsSq]
  · simp [ZMod.card, sq]
end Formalism.LFunctionChainParameters.ProjectiveLineModels
