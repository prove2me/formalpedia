-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.weightProd_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:06:02.787855+00:00
-- url     : https://prove2.me/submissions/234c3b76-49b8-49fc-8cd7-4ff56cc6d12f

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
theorem _root_.solution : WeightProd := by
  intro r c
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1),
      Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1), mul_pow, ← Finset.prod_pow, ← mul_assoc,
      ← Finset.prod_mul_distrib]
    congr 1
    · apply Finset.prod_congr rfl
      intro a ha
      rw [Finset.mem_Icc] at ha
      rw [← pow_add]; congr 1; omega
    · congr 1; omega
end Formalism.HermitianLatticeCounting.P
