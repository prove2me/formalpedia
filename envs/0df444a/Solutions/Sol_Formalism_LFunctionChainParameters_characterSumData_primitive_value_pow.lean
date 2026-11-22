-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.primitive_value_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:47.503801+00:00
-- url     : https://prove2.me/submissions/79f4ff2d-6858-490f-94dd-df93d56250cc

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution : PrimValPow (H := H) := by
  intro D ψ p i hp hi
  unfold primVal
  first
  | rw [Nat.primeFactors_prime_pow (by omega) hp, Finset.prod_singleton, hp.factorization_pow,
      Finsupp.single_eq_same]
  | simp [Nat.primeFactors_prime_pow (by omega : i ≠ 0) hp, hp.factorization_pow]
end Formalism.LFunctionChainParameters.characterSumData
