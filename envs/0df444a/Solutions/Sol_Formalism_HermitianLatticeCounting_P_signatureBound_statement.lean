-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.signatureBound_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:07:46.946799+00:00
-- url     : https://prove2.me/submissions/3ede1d97-68e9-42da-97bf-a36efb0715d8

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : SignatureBound := by
  intro V _ _ _ h A Pos hA hP
  have hd : Disjoint A Pos := by
    rw [Submodule.disjoint_def]
    intro x hxA hxP
    by_contra hx
    exact absurd (hA x hxA) (not_le.mpr (hP x hxP hx))
  exact Submodule.finrank_add_finrank_le_of_disjoint hd
end Formalism.HermitianLatticeCounting.P
