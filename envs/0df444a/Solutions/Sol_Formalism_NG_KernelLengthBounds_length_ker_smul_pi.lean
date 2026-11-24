-- Prove2me | solution 1 for Formalism.NG.KernelLengthBounds.length_ker_smul_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:13.846459+00:00
-- url     : https://prove2.me/submissions/6c116bfa-6d7d-49fa-bf50-22be2d3f65b0

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Theorems.Thm_Formalism_NG_lenKer


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
open Formalism.NG.KernelLengthBounds
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG.KernelLengthBounds
theorem _root_.solution (d : Type) [Fintype d] (a : O) :
    Module.length O (LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) a)) =
      (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O a := by
  classical
  have hA : DistribSMul.toLinearMap O (d → KO O) a = matQ O (Matrix.diagonal fun _ : d => a) := by
    apply LinearMap.ext
    intro v
    funext i
    show a • v i = ∑ j, Matrix.diagonal (fun _ : d => a) i j • v j
    rw [Finset.sum_eq_single i
      (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), zero_smul])
      (fun h => (h (Finset.mem_univ i)).elim), Matrix.diagonal_apply_eq]
  rw [hA, (lenKer : StatLenKer) O d, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul]
end Formalism.NG.KernelLengthBounds
