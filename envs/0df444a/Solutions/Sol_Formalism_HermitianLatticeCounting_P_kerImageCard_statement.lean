-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.kerImageCard_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:47.325799+00:00
-- url     : https://prove2.me/submissions/f5567c4d-6049-49a0-9226-4e6c9cf6030e

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
theorem _root_.solution : KerImageCard := by
  intro A C _ _ _ φ K S hK hS
  have h1 : Nat.card A = Nat.card φ.range * Nat.card φ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
  have : Finite φ.range := Set.finite_range φ
  have h2 : Nat.card K ≤ Nat.card φ.ker := AddSubgroup.card_le_of_le hK
  have h3 : Nat.card S ≤ Nat.card φ.range := AddSubgroup.card_le_of_le hS
  rw [h1, mul_comm]; exact Nat.mul_le_mul h3 h2
end Formalism.HermitianLatticeCounting.P
