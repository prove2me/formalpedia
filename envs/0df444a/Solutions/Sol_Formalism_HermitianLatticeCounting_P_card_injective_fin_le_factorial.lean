-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.card_injective_fin_le_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:41.509255+00:00
-- url     : https://prove2.me/submissions/bc61cea6-c2a0-4958-8fa2-8f66010cb8ef

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (t N : ℕ) :
    (Finset.univ.filter (fun f : Fin t → Fin N => Function.Injective f)).card ≤ N.factorial := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  by_cases h : t ≤ N
  · rw [← Nat.factorial_mul_descFactorial h]
    exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]; exact Nat.zero_le _
end Formalism.HermitianLatticeCounting.P
