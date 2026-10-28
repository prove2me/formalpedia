-- Prove2me | solution 1 for D1Bound5.finitePPairTail_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:52.003607+00:00
-- url     : https://prove2.me/submissions/cc61b7de-0b03-46ef-990c-47cc6649e1de

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
import Definitions.Def_D1Bound5_FinitePTailCoefficients_Definitions
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions
import Theorems.Thm_D1Bound5_finitePHalfRemainder_norm_le
import Theorems.Thm_D1Bound5_finitePPairCoeff_norm_le
import Theorems.Thm_D1Bound5_finitePTailCoeffWeight_sum

section
namespace D1Bound5

private theorem finitePPairTail_summand_norm_le (u v c : ℂ) (A S : ℝ)
    (hA1 : 1 ≤ A) (hAu : A ≤ ‖u‖) (hAv : A ≤ ‖v‖)
    (huS : ‖u‖ ≤ S) (hvS : ‖v‖ ≤ S) (hAC : 1000 ≤ A*‖c‖)
    (kind side : Fin 2) (l : Fin 3) :
    ‖![u,v] side*finitePPairCoeff u v kind side l*c^(l : ℕ)*
      finiteQHalfRemainder (6+(l : ℕ)) (1/(![u,v] side*c))‖ ≤
    (finitePTailCoeffWeight kind side l : ℝ)*
      ((21/1024 : ℝ)*(1000/999)*S^2/(A^4*‖c‖^6)) := by
  let U := ‖![u,v] side‖
  let C := ‖c‖
  have hAU : A ≤ U := by fin_cases side <;> assumption
  have hA : 0 < A := by linarith only [hA1]
  have hU : 0 < U := hA.trans_le hAU
  have hC : 0 < C := by
    have hn : 0 ≤ C := norm_nonneg c
    by_contra h
    have he : C=0 := le_antisymm (le_of_not_gt h) hn
    change 1000 ≤ A*C at hAC
    rw [he,mul_zero] at hAC
    norm_num at hAC
  have hUC : 1000 ≤ U*C := hAC.trans (mul_le_mul_of_nonneg_right hAU hC.le)
  have hn : ‖1/(![u,v] side*c)‖ = 1/(U*C) := by simp [U,C,norm_div,norm_mul]
  have hr : 1/(U*C) ≤ (1/1000 : ℝ) :=
    (div_le_div_iff₀ (mul_pos hU hC) (by norm_num)).mpr (by simpa using hUC)
  have hradius : ‖1/(![u,v] side*c)‖ < 1 := by rw [hn]; linarith only [hr]
  have hrem := finitePHalfRemainder_norm_le (6+(l : ℕ)) (1/(![u,v] side*c))
    (by omega) hradius
  rw [hn] at hrem
  have heta : 0 < 1-1/(U*C) := by linarith only [hr]
  have hinv : 1/(1-1/(U*C)) ≤ (1000/999 : ℝ) :=
    (div_le_iff₀ heta).mpr (by linarith only [hr])
  have hr0 : 0 ≤ 1/(U*C) := by positivity
  have hrem' : ‖finiteQHalfRemainder (6+(l : ℕ)) (1/(![u,v] side*c))‖ ≤
      (21/1024 : ℝ)*(1/(U*C))^(6+(l : ℕ))*(1000/999) := by
    apply hrem.trans
    have hm := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ (21/1024 : ℝ)*(1/(U*C))^(6+(l : ℕ)) by positivity)
    convert hm using 1 <;> ring
  have hcoeff := finitePPairCoeff_norm_le u v A S hA1 hAu hAv huS hvS kind side l
  calc
    _ = U*‖finitePPairCoeff u v kind side l‖*C^(l : ℕ)*
        ‖finiteQHalfRemainder (6+(l : ℕ)) (1/(![u,v] side*c))‖ := by
      simp only [norm_mul,norm_pow,U,C]
    _ ≤ U*((finitePTailCoeffWeight kind side l : ℝ)*(S^2/A^4)*U^(5+(l : ℕ)))*
        C^(l : ℕ)*((21/1024 : ℝ)*(1/(U*C))^(6+(l : ℕ))*(1000/999)) := by
      gcongr
    _ = _ := by
      have hcn : ‖c‖ ≠ 0 := hC.ne'
      fin_cases l <;> norm_num [C] <;>
        field_simp [hA.ne', hU.ne', hcn] <;> ring

/-- Actual Taylor tails for the two pair-row types, with the exact finite
absolute-coefficient totals876 and2676. -/
theorem _root_.solution (u v c : ℂ) (A S : ℝ)
    (hA1 : 1 ≤ A) (hAu : A ≤ ‖u‖) (hAv : A ≤ ‖v‖)
    (huS : ‖u‖ ≤ S) (hvS : ‖v‖ ≤ S) (hAC : 1000 ≤ A*‖c‖) (kind : Fin 2) :
    ‖finitePPairTail u v c kind‖ ≤ (![876,2676] kind : ℕ)*
      ((21/1024 : ℝ)*(1000/999)*S^2/(A^4*‖c‖^6)) := by
  unfold finitePPairTail
  calc
    _ ≤ ∑ side : Fin 2, ∑ l : Fin 3,
        ‖![u,v] side*finitePPairCoeff u v kind side l*c^(l : ℕ)*
          finiteQHalfRemainder (6+(l : ℕ)) (1/(![u,v] side*c))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun side _ => norm_sum_le _ _))
    _ ≤ ∑ side : Fin 2, ∑ l : Fin 3, (finitePTailCoeffWeight kind side l : ℝ)*
        ((21/1024 : ℝ)*(1000/999)*S^2/(A^4*‖c‖^6)) := by
      apply Finset.sum_le_sum
      intro side _
      apply Finset.sum_le_sum
      intro l _
      exact finitePPairTail_summand_norm_le u v c A S hA1 hAu hAv huS hvS hAC kind side l
    _ = _ := by
      simp only [← Finset.sum_mul,← Nat.cast_sum]
      rw [finitePTailCoeffWeight_sum]



end D1Bound5
end
