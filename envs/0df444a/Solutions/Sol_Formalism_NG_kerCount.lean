-- Prove2me | solution 1 for Formalism.NG.kerCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:39.691081+00:00
-- url     : https://prove2.me/submissions/b24c5af6-53ce-4d7c-a154-c06be6a061d5

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Theorems.Thm_Formalism_NG_KernelLengthBounds_length_colData_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatKerCount := by
  intro O _ _ _ Hk _ _ ι cols ℓ δ e' j d _ Xw _ _ h0 hX f hf
  classical
  refine (Module.length_le_of_injective f hf).trans ?_
  rw [Module.length_pi_of_fintype,
    Finset.sum_coe_sort cols (fun w => Module.length O (ColData O ℓ δ (e' w) (j w) (Xw w) d))]
  refine (Finset.sum_le_sum fun w _ =>
    KernelLengthBounds.length_colData_le ℓ δ (e' w) (j w) (Xw w) d (h0 w) (hX w)).trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_assoc]
end Formalism.NG
