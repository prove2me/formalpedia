-- Prove2me | solution 1 for Formalism.NG.gen_relMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:36.642365+00:00
-- url     : https://prove2.me/submissions/9ce03a60-04b4-4cf4-9589-53abb79bb67c

import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
import Theorems.Thm_Formalism_NG_gen_relMap_apply

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
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG
theorem _root_.solution {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (X : Matrix a b O) (Y : Matrix b c O) :
    relMap O (KO O) (X * Y) = relMap O (KO O) X ∘ₗ relMap O (KO O) Y := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [LinearMap.comp_apply, gen_relMap_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm
end Formalism.NG
