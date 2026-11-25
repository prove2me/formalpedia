-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integer_group_local_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:05.425226+00:00
-- url     : https://prove2.me/submissions/7f3a01e5-86c1-40a8-84af-427ca6a9d02b

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LocalIntegralStructure_zZgPreserve


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
theorem _root_.solution : ZZgLocal := by
  intro E _ _ g a b c d P h hg
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩, ⟨x4, h4⟩, _⟩ := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.zZgPreserve E g a b c d h
  exact ⟨⟨g, x1, hg, by simp [h1]⟩, ⟨g, x2, hg, by simp [h2]⟩, ⟨g, x3, hg, by simp [h3]⟩,
    ⟨g, x4, hg, by simp [h4]⟩⟩
end Formalism.HermitianLatticeCounting.P
