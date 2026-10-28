-- Prove2me | solution 1 for D1Bound5.finitePTail_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:46.547782+00:00
-- url     : https://prove2.me/submissions/b7eab5ce-d075-4998-a66e-494220a426b7

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
import Theorems.Thm_D1Bound5_finitePPairTail_norm_le

section
namespace D1Bound5





/-- Every actual P-row tail is strictly below one eighth of the common
residual scale. No coefficient or analytic bound is assumed in the statement. -/
theorem _root_.solution (a b s c : ℂ)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hAC : 1000 ≤ ‖a‖*‖c‖) (i : Fin 4) :
    ‖finitePTail a b s c i‖ < (1/8 : ℝ)*‖s‖^2/(‖a‖^3*‖c‖^5) := by
  have hAS : ‖a‖ ≤ ‖s‖ := hAB.trans hBS
  have hA0 : 0 < ‖a‖ := by linarith only [hA]
  have hS0 : 0 < ‖s‖ := hA0.trans_le hAS
  have hC0 : 0 < ‖c‖ := by
    by_contra h
    have he : ‖c‖=0 := le_antisymm (le_of_not_gt h) (norm_nonneg c)
    rw [he,mul_zero] at hAC
    norm_num at hAC
  let K : ℝ := (21/1024 : ℝ)*(1000/999)*‖s‖^2/(‖a‖^4*‖c‖^6)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have habR : ‖finitePPairTail a b c 0‖ ≤ 876*K :=
    finitePPairTail_norm_le a b c ‖a‖ ‖s‖ hA le_rfl hAB hAS hBS hAC 0
  have hbsR : ‖finitePPairTail b s c 0‖ ≤ 876*K :=
    finitePPairTail_norm_le b s c ‖a‖ ‖s‖ hA hAB hAS hBS le_rfl hAC 0
  have hasR : ‖finitePPairTail a s c 0‖ ≤ 876*K :=
    finitePPairTail_norm_le a s c ‖a‖ ‖s‖ hA le_rfl hAS hAS le_rfl hAC 0
  have habT : ‖finitePPairTail a b c 1‖ ≤ 2676*K :=
    finitePPairTail_norm_le a b c ‖a‖ ‖s‖ hA le_rfl hAB hAS hBS hAC 1
  have hasT : ‖finitePPairTail a s c 1‖ ≤ 2676*K :=
    finitePPairTail_norm_le a s c ‖a‖ ‖s‖ hA le_rfl hAS hAS le_rfl hAC 1
  have hbsT : ‖finitePPairTail b s c 1‖ ≤ 2676*K :=
    finitePPairTail_norm_le b s c ‖a‖ ‖s‖ hA hAB hAS hBS le_rfl hAC 1
  have hrow : ‖finitePTail a b s c i‖ ≤ 5352*K := by
    fin_cases i
    · exact habR.trans (by nlinarith only [hK])
    · change ‖finitePPairTail a b c 0+finitePPairTail b s c 0-finitePPairTail a s c 0‖ ≤ _
      have hnorm := norm_sub_le (finitePPairTail a b c 0+finitePPairTail b s c 0)
        (finitePPairTail a s c 0)
      have hadd := norm_add_le (finitePPairTail a b c 0) (finitePPairTail b s c 0)
      linarith only [hnorm,hadd,habR,hbsR,hasR,hK]
    · exact habT.trans (by nlinarith only [hK])
    · change ‖finitePPairTail a s c 1-finitePPairTail b s c 1‖ ≤ _
      exact (norm_sub_le _ _).trans (by linarith only [hasT,hbsT])
  apply hrow.trans_lt
  have hratio : 1000/(‖a‖*‖c‖) ≤ 1 :=
    (div_le_one (mul_pos hA0 hC0)).mpr hAC
  have halg : 5352*K = (112392/1022976 : ℝ)*(1000/(‖a‖*‖c‖))*
      (‖s‖^2/(‖a‖^3*‖c‖^5)) := by
    dsimp [K]
    field_simp [hA0.ne',hC0.ne']
    <;> ring
  rw [halg]
  calc
    _ ≤ (112392/1022976 : ℝ)*1*(‖s‖^2/(‖a‖^3*‖c‖^5)) := by gcongr
    _ < (1/8 : ℝ)*(‖s‖^2/(‖a‖^3*‖c‖^5)) := by
      exact mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ = _ := by ring

end D1Bound5
end
