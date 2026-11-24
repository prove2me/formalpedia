-- Prove2me | solution 1 for Formalism.NG.gen_relMap_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:38.127879+00:00
-- url     : https://prove2.me/submissions/8ccfd8da-10d2-4125-bcec-c18045eb50ae

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
theorem _root_.solution {a : Type*} [Fintype a] [DecidableEq a] (v : a → KO O) :
    relMap O (KO O) (1 : Matrix a a O) v = v := by
  funext i
  simp [gen_relMap_apply, Matrix.one_apply, ite_smul]
end Formalism.NG
