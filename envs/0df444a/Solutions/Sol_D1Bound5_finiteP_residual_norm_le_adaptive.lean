-- Prove2me | solution 1 for D1Bound5.finiteP_residual_norm_le_adaptive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:28:56.018369+00:00
-- url     : https://prove2.me/submissions/fe5d4734-43b2-4777-9fb2-27ac6d1a2ed2

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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveLeading_Definitions
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FinitePAdaptiveTailData_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
import Theorems.Thm_D1Bound5_finitePAdaptiveTailWeight_eq
import Theorems.Thm_D1Bound5_finitePAdaptiveTailWeight_le_last
import Theorems.Thm_D1Bound5_finitePLeading_norm_le_adaptive
import Theorems.Thm_D1Bound5_finitePResidual_eq_leading_tail
import Theorems.Thm_D1Bound5_finitePTail_adaptive_norm_le

section
namespace D1Bound5



theorem finitePLeadingWeight_le_last (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (i : Fin 4) : finitePLeadingWeight x i ≤ finitePLeadingWeight x 3 := by
  have h54 : x^5 ≤ x^4 := by
    have h := mul_le_mul_of_nonneg_left hx1 (pow_nonneg hx0 4)
    nlinarith only [h]
  fin_cases i <;> norm_num [finitePLeadingWeight,Matrix.cons_val_three]
  all_goals nlinarith only [h54,hx0,pow_nonneg hx0 2,pow_nonneg hx0 3,pow_nonneg hx0 4]



theorem finitePAdaptiveRate_eq_last (x : ℝ) :
    finitePAdaptiveRate x = finitePLeadingWeight x 3+
      (21/(1024*999) : ℝ)*finitePAdaptiveTailWeight 3 x := by
  rw [finitePAdaptiveTailWeight_eq]
  rfl

theorem finitePAdaptiveRate_mono (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    finitePAdaptiveRate x ≤ finitePAdaptiveRate y := by
  unfold finitePAdaptiveRate
  gcongr



/-- Exact adaptive bound on the actual principal-root residual. -/
theorem _root_.solution (a b s c : ℂ)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hAC : 1000 ≤ ‖a‖*‖c‖) (q : ℝ) (hq : 1 ≤ q) (hqab : q*‖a‖ ≤ ‖b‖)
    (i : Fin 4) :
    ‖finitePResidual a b s c i‖ ≤
      finitePAdaptiveRate (1/q)*‖s‖^2/(‖a‖^3*‖c‖^5) := by
  have hA0 : 0 < ‖a‖ := by linarith only [hA]
  have hB0 : 0 < ‖b‖ := hA0.trans_le hAB
  have hS0 : 0 < ‖s‖ := hB0.trans_le hBS
  have hC0 : 0 < ‖c‖ := by
    by_contra h
    have he : ‖c‖=0 := le_antisymm (le_of_not_gt h) (norm_nonneg c)
    rw [he,mul_zero] at hAC
    norm_num at hAC
  have hq0 : 0 < q := by linarith only [hq]
  let x := ‖a‖/‖b‖
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := (div_le_one hB0).mpr hAB
  have hxq : x ≤ 1/q := (div_le_div_iff₀ hB0 hq0).mpr (by simpa [mul_comm] using hqab)
  have hlead := finitePLeading_norm_le_adaptive a b s hA hAB hBS i
  have htail := finitePTail_adaptive_norm_le a b s c hA hAB hBS hAC i
  have hL := finitePLeadingWeight_le_last x hx0 hx1 i
  have hW := finitePAdaptiveTailWeight_le_last x hx0 hx1 i
  rw [finitePResidual_eq_leading_tail a b s c (norm_pos_iff.mp hA0)
    (norm_pos_iff.mp hB0) (norm_pos_iff.mp hS0) (norm_pos_iff.mp hC0) i]
  calc
    _ ≤ ‖finitePLeading a b s i/c^5‖+‖finitePTail a b s c i‖ := norm_add_le _ _
    _ = ‖finitePLeading a b s i‖/‖c‖^5+‖finitePTail a b s c i‖ := by rw [norm_div,norm_pow]
    _ ≤ (finitePLeadingWeight x i*(‖s‖^2/‖a‖^3))/‖c‖^5+
        (21/(1024*999) : ℝ)*finitePAdaptiveTailWeight i x*‖s‖^2/(‖a‖^3*‖c‖^5) :=
      add_le_add (div_le_div_of_nonneg_right hlead (by positivity)) htail
    _ ≤ (finitePLeadingWeight x 3*(‖s‖^2/‖a‖^3))/‖c‖^5+
        (21/(1024*999) : ℝ)*finitePAdaptiveTailWeight 3 x*‖s‖^2/(‖a‖^3*‖c‖^5) := by
      gcongr
    _ = finitePAdaptiveRate x*‖s‖^2/(‖a‖^3*‖c‖^5) := by rw [finitePAdaptiveRate_eq_last]; ring
    _ ≤ finitePAdaptiveRate (1/q)*‖s‖^2/(‖a‖^3*‖c‖^5) := by
      gcongr
      exact finitePAdaptiveRate_mono x (1/q) hx0 hxq

end D1Bound5
end
