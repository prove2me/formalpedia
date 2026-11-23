-- Prove2me | solution 1 for Formalism.D5.Bal.askC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:52.644803+00:00
-- url     : https://prove2.me/submissions/69385acc-455d-42c2-901a-6df79f3f8249

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
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
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5.Bal
theorem _root_.solution (Hs : CycHost H) (ψ : AddChar (E0 × H) ℂ) (a w : ℝ) (ha : 0 < a) (hw : 0 < w) :
    ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w : ℝ) : ℂ)
      = (w : ℂ) * GC Hs ψ (a / w) + (if ψ = 0 then
          ((a * Real.log a - a * Real.log w - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * Hs.ell ψ) := by
  have hw0 : w ≠ 0 := hw.ne'
  have hterm : ∀ n : ℕ, ((a / n - w : ℝ) : ℂ) = (w : ℂ) * ((a / w / n - 1 : ℝ) : ℂ) := by
    intro n
    rw [term_real a w hw0 n, Complex.ofReal_mul]
  have hwaR : w * (a / w) = a := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hw0, mul_one]
  by_cases hψ : ψ = 0
  · subst hψ
    have key : w * Formalism.Gz (a / w) + (a * Real.log a - a * Real.log w - (1 + Real.eulerMascheroniConstant) * a)
        = w * Formalism.Sz (a / w) := by
      rw [Formalism.Gz, Real.log_div ha.ne' hw0]
      linear_combination (-(Real.log a - Real.log w) + (1 + Real.eulerMascheroniConstant)) * hwaR
    have hL : ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv 0 n * ((a / n - w : ℝ) : ℂ)
        = ((w * Formalism.Sz (a / w) : ℝ) : ℂ) := by
      rw [Formalism.Sz, Finset.mul_sum, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Hs.2 n, hterm n, Complex.ofReal_mul, Complex.ofReal_mul]
      ring
    rw [hL, GC, if_pos rfl, if_pos rfl, ← key, Complex.ofReal_add, Complex.ofReal_mul]
  · have hS : ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w : ℝ) : ℂ)
        = (w : ℂ) * ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / w / n - 1 : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [hterm n]
      ring
    have hwa : (w : ℂ) * ((a / w : ℝ) : ℂ) = (a : ℂ) := by
      rw [← Complex.ofReal_mul, hwaR]
    rw [hS, if_neg hψ, GC, if_neg hψ]
    linear_combination (-(Hs.ell ψ)) * hwa
end Formalism.D5.Bal
