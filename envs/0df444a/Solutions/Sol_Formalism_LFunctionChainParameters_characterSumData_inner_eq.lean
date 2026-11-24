-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:55.068537+00:00
-- url     : https://prove2.me/submissions/3d9f4a23-e736-402c-8dcd-5f67fc6bf695

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_primitive_value_trivial
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_term_real
import Theorems.Thm_Formalism_D5_Bal_term_real


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
theorem _root_.solution (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) :
    ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * primVal D ψ n * ((a / n - w : ℝ) : ℂ)
      = (w : ℂ) * GPsi D ell ψ (a / w) + (if ψ = 0 then
          ((a * Real.log a - a * Real.log w - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * ell ψ) := by
  unfold GPsi
  split_ifs with h0
  · subst h0
    simp only [Gz, Sz]
    simp_rw [primitive_value_trivial D, mul_one, ← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_add]
    congr 1
    have hS : w * ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * (a / w / n - 1)
        = ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * (a / n - w) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [term_real a w hw.ne' n]
      ring
    have hwa' : w * (a / w) = a := by field_simp
    rw [Real.log_div ha.ne' hw.ne', ← hS]
    linear_combination (Real.log a - Real.log w - (1 + Real.eulerMascheroniConstant)) * hwa'
  · have hwa' : w * (a / w) = a := by field_simp
    have hwa : (w : ℂ) * ((a / w : ℝ) : ℂ) = a := by
      rw [← Complex.ofReal_mul, hwa']
    rw [mul_add, Finset.mul_sum]
    have hs : ∀ n ∈ Icc 1 ⌊a / w⌋₊, (w : ℂ) * ((Λ n : ℂ) * primVal D ψ n * ((a / w / n - 1 : ℝ) : ℂ))
        = (Λ n : ℂ) * primVal D ψ n * ((a / n - w : ℝ) : ℂ) := by
      intro n _
      rw [term_real a w hw.ne' n]
      push_cast
      ring
    rw [Finset.sum_congr rfl hs, ← mul_assoc, hwa]
    ring
end Formalism.LFunctionChainParameters.characterSumData
