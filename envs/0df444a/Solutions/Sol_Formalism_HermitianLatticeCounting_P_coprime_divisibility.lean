-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.coprime_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:32.8928+00:00
-- url     : https://prove2.me/submissions/32bdf817-03df-41d4-8195-4ab49379f0ce

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
theorem _root_.solution : CoprimeDiv := by
  intro R _ g T c hco h
  have h0 : IsCoprime ((g : ℤ)) ((T : ℤ)) := Nat.isCoprime_iff_coprime.mpr hco
  have h1 : IsCoprime (g : R) (T : R) := by
    have := h0.map (Int.castRingHom R)
    simpa using this
  exact h1.dvd_of_dvd_mul_right h
end Formalism.HermitianLatticeCounting.P
