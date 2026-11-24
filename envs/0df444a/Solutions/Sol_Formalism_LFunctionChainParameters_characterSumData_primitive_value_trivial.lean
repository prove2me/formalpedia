-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.primitive_value_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:46.118043+00:00
-- url     : https://prove2.me/submissions/28400d98-e7cc-4f84-b681-93696f7c3393

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
section
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
namespace PB
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private theorem zero_apply_lemma (g : E0 × H) : (0 : AddChar (E0 × H) ℂ) g = 1 := by
  first
  | exact AddChar.zero_apply g
  | rfl
  | simp
end
end PB
open PB
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
end Formalism.LFunctionChainParameters.characterSumData
end
end

set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution : PrimValTriv (H := H) := by
  intro D n
  unfold primVal
  refine Finset.prod_eq_one (fun p _ => ?_)
  unfold cosetMean
  simp only [zero_apply_lemma, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine div_self ?_
  rw [Nat.cast_ne_zero]
  exact Finset.card_ne_zero.mpr ⟨0, by simp⟩
end Formalism.LFunctionChainParameters.characterSumData
