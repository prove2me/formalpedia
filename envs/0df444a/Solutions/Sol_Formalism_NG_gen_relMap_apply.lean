-- Prove2me | solution 1 for Formalism.NG.gen_relMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:16.966489+00:00
-- url     : https://prove2.me/submissions/75bc72c2-de04-4926-8b11-9fb2b141fda0

import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply

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
theorem _root_.solution {a b : Type*} [Fintype a] [Fintype b] (X : Matrix a b O) (v : b → KO O) (i : a) :
    relMap O (KO O) X v i = ∑ j, X i j • v j := rfl
end Formalism.NG
