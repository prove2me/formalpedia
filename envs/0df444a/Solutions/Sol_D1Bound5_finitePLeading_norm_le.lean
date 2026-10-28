-- Prove2me | solution 1 for D1Bound5.finitePLeading_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:44.278855+00:00
-- url     : https://prove2.me/submissions/ba182523-2348-47b5-88cd-498a186db310

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
import Definitions.Def_D1Bound5_FinitePLeadingBound_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
import Theorems.Thm_D1Bound5_finiteP_monomial_bound

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three







theorem finitePLeading_eq_terms (a b s : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hs : s ≠ 0) (i : Fin 4) :
    finitePLeading a b s i =
      (∑ t, finitePLeadingTermValue ![a,b,s] (finitePLeadingTerms i t))/256 := by
  fin_cases i <;> norm_num [finitePLeading,finitePLeadingR,finitePLeadingT,
    finitePLeadingV,finitePLeadingTerms,finitePLeadingTermValue,Fin.sum_univ_succ]
  all_goals field_simp [ha,hb,hs] <;> ring

theorem finitePLeadingTerms_exponents (i : Fin 4) (t : Fin 12) :
    let u := finitePLeadingTerms i t
    u.2.2.2.1 ≤ 2 ∧ u.2.2.2.1+3 ≤ u.2.2.2.2+2 := by
  fin_cases i <;> fin_cases t <;> norm_num [finitePLeadingTerms]

theorem finitePLeadingTerms_sum (i : Fin 4) :
    (∑ t, |((finitePLeadingTerms i t).1 : ℝ)|) ≤ 560 := by
  fin_cases i <;> norm_num [finitePLeadingTerms,Fin.sum_univ_succ]

theorem _root_.solution (a b s : ℂ)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖) (i : Fin 4) :
    ‖finitePLeading a b s i‖ ≤ (35/16 : ℝ)*‖s‖^2/‖a‖^3 := by
  have hapos : 0 < ‖a‖ := by linarith
  have hbpos : 0 < ‖b‖ := hapos.trans_le hAB
  have hspos : 0 < ‖s‖ := hbpos.trans_le hBS
  have hlow (j : Fin 3) : ‖a‖ ≤ ‖![a,b,s] j‖ := by
    fin_cases j
    · exact le_rfl
    · exact hAB
    · exact hAB.trans hBS
  have hupp (j : Fin 3) : ‖![a,b,s] j‖ ≤ ‖s‖ := by
    fin_cases j
    · exact hAB.trans hBS
    · exact hBS
    · exact le_rfl
  have hterm (t : Fin 12) :
      ‖finitePLeadingTermValue ![a,b,s] (finitePLeadingTerms i t)‖ ≤
        |((finitePLeadingTerms i t).1 : ℝ)| *(‖s‖^2/‖a‖^3) := by
    let u := finitePLeadingTerms i t
    obtain ⟨he,hn⟩ := finitePLeadingTerms_exponents i t
    have hm := finiteP_monomial_bound ‖a‖ ‖s‖ ‖![a,b,s] u.2.1‖ ‖![a,b,s] u.2.2.1‖
      3 u.2.2.2.2 0 u.2.2.2.1 hA (hlow _) (hlow _) (hupp _) (hupp _) he (by simpa using hn)
    have hnorm : ‖(u.1 : ℂ)‖ = |(u.1 : ℝ)| := by simp
    simpa [finitePLeadingTermValue, norm_div, norm_mul, norm_pow, hnorm,
      pow_zero, one_mul, mul_div_assoc, u] using
        mul_le_mul_of_nonneg_left hm (abs_nonneg (u.1 : ℝ))
  rw [finitePLeading_eq_terms a b s (norm_pos_iff.mp hapos)
    (norm_pos_iff.mp hbpos) (norm_pos_iff.mp hspos) i, norm_div]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (∑ t, |((finitePLeadingTerms i t).1 : ℝ)| *(‖s‖^2/‖a‖^3))/256 := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => hterm t)
    _ = (∑ t, |((finitePLeadingTerms i t).1 : ℝ)|)*(‖s‖^2/‖a‖^3)/256 := by
      rw [Finset.sum_mul]
    _ ≤ 560*(‖s‖^2/‖a‖^3)/256 := by
      gcongr
      exact finitePLeadingTerms_sum i
    _ = _ := by ring

end D1Bound5
end
