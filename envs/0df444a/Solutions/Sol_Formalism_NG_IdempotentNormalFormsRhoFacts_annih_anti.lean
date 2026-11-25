-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.annih_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:36.792934+00:00
-- url     : https://prove2.me/submissions/5496d26e-f08b-4c62-a7b6-2a1a495b02e4

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_mem_annih

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
open Formalism.NG.IdempotentNormalFormsRhoFacts
namespace Formalism.NG.IdempotentNormalFormsRhoFacts
theorem _root_.solution {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw]
    [AddCommGroup Cs] [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P)
    {U V : Submodule O Cs} (h : U ≤ V) : annih pr V ≤ annih pr U := fun c hc =>
  (mem_annih pr U c).2 fun x hx => (mem_annih pr V c).1 hc x (h hx)
end Formalism.NG.IdempotentNormalFormsRhoFacts
