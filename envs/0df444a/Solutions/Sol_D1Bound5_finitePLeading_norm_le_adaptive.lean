-- Prove2me | solution 1 for D1Bound5.finitePLeading_norm_le_adaptive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:11.133698+00:00
-- url     : https://prove2.me/submissions/36fb5332-7afc-4b87-9313-e376905b668c

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
import Definitions.Def_D1Bound5_FinitePAdaptiveLeading_Definitions
import Definitions.Def_D1Bound5_FinitePLeadingBound_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
import Theorems.Thm_D1Bound5_finitePAdaptiveLeading_exponents
import Theorems.Thm_D1Bound5_finitePLeadingWeight_eq_sum
import Theorems.Thm_D1Bound5_finiteP_ratio_monomial_bound

section
namespace D1Bound5











theorem finitePAdaptiveLeading_eq_terms (a b s : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (i : Fin 4) :
    finitePLeading a b s i =
      (∑ t, finitePAdaptiveLeadingTermValue a b s (finitePAdaptiveLeadingTerms i t))/256 := by
  fin_cases i <;> norm_num [finitePLeading,finitePLeadingR,finitePLeadingT,
    finitePLeadingV,finitePAdaptiveLeadingTerms,finitePLeadingTerms,
    finitePAdaptiveLeadingTermValue,finitePLeadingNumeratorExponent,Fin.sum_univ_succ,
    Fin.ext_iff,Matrix.cons_val_two]
  all_goals field_simp [ha,hb,hs] <;> ring





/-- Actual leading residual coefficient with the exact ratio-sensitive
positive polynomial, rather than the coarser uniform constant35/16. -/
theorem _root_.solution (a b s : ℂ)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖) (i : Fin 4) :
    ‖finitePLeading a b s i‖ ≤
      finitePLeadingWeight (‖a‖/‖b‖) i*(‖s‖^2/‖a‖^3) := by
  have hA0 : 0 < ‖a‖ := by linarith only [hA]
  have hB0 : 0 < ‖b‖ := hA0.trans_le hAB
  have hS0 : 0 < ‖s‖ := hB0.trans_le hBS
  have ht (t : Fin 12) :
      ‖finitePAdaptiveLeadingTermValue a b s (finitePAdaptiveLeadingTerms i t)‖ ≤
        |((finitePAdaptiveLeadingTerms i t).1 : ℝ)| *
          (‖a‖/‖b‖)^(finitePLeadingRatioExponent (finitePAdaptiveLeadingTerms i t))*
            (‖s‖^2/‖a‖^3) := by
    let u := finitePAdaptiveLeadingTerms i t
    let p := finitePLeadingNumeratorExponent u
    obtain ⟨hdeg,he,hl⟩ := finitePAdaptiveLeading_exponents i t
    have hmono := finiteP_ratio_monomial_bound ‖a‖ ‖b‖ ‖s‖ hA hAB hBS
      u.2.1 (p 0) (p 1) (p 2) u.2.2.2.2 3 (finitePLeadingRatioExponent u)
      hdeg he hl
    have hn : ‖(u.1 : ℂ)‖ = |(u.1 : ℝ)| := by simp
    have hanchor : ‖![a,b,s] u.2.1‖ = ![‖a‖,‖b‖,‖s‖] u.2.1 := by
      generalize u.2.1 = r
      fin_cases r <;> rfl
    have hh := mul_le_mul_of_nonneg_left hmono (abs_nonneg (u.1 : ℝ))
    change ‖(u.1 : ℂ)*a^(p 0)*b^(p 1)*s^(p 2)/(![a,b,s] u.2.1)^u.2.2.2.2‖ ≤ _
    simp only [norm_div,norm_mul,norm_pow,hn,hanchor]
    calc
      _ = |(u.1 : ℝ)| *(‖a‖^(p 0)*‖b‖^(p 1)*‖s‖^(p 2)/
          (![‖a‖,‖b‖,‖s‖] u.2.1)^u.2.2.2.2) := by ring
      _ ≤ |(u.1 : ℝ)| *((‖s‖^2/‖a‖^3)*
          (‖a‖/‖b‖)^(finitePLeadingRatioExponent u)) := hh
      _ = _ := by ring
  rw [finitePAdaptiveLeading_eq_terms a b s (norm_pos_iff.mp hA0)
    (norm_pos_iff.mp hB0) (norm_pos_iff.mp hS0) i,norm_div]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (∑ t, |((finitePAdaptiveLeadingTerms i t).1 : ℝ)| *
          (‖a‖/‖b‖)^(finitePLeadingRatioExponent (finitePAdaptiveLeadingTerms i t))*
            (‖s‖^2/‖a‖^3))/256 := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ht t)
    _ = finitePLeadingWeight (‖a‖/‖b‖) i*(‖s‖^2/‖a‖^3) := by
      rw [← Finset.sum_mul,finitePLeadingWeight_eq_sum]
      ring

end D1Bound5
end
