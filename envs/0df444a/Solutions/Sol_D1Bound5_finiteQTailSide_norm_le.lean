-- Prove2me | solution 1 for D1Bound5.finiteQTailSide_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:53:09.957156+00:00
-- url     : https://prove2.me/submissions/8e444556-fb40-49d3-8c3f-84db8b5045f1

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQResidualBound_Definitions
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions
import Theorems.Thm_D1Bound5_finiteQHalfRemainder_norm_le

section
namespace D1Bound5

theorem finiteQHalfRemainder_small_norm_le (n : ℕ) (z : ℂ)
    (hn : 4 ≤ n) (hz : ‖z‖ ≤ (1/1000 : ℝ)) :
    ‖finiteQHalfRemainder n z‖ ≤ (625/15984 : ℝ)*‖z‖^n := by
  have hz1 : ‖z‖ < 1 := by linarith
  apply (finiteQHalfRemainder_norm_le n z hn hz1).trans
  apply (div_le_iff₀ (sub_pos.mpr hz1)).2
  have hm := mul_le_mul_of_nonneg_right hz (pow_nonneg (norm_nonneg z) n)
  nlinarith only [hm]



/-- Each of the two anchor sides is bounded using its actual fourth- and
fifth-order Taylor tails. Cancellation of the anchor and c powers leaves
exactly the monomials1/U and V/U². -/
theorem _root_.solution
    (u v c : ℂ) (A T : ℝ) (hA : 0 < A)
    (hAu : A ≤ ‖u‖) (huT : ‖u‖ ≤ T) (hvT : ‖v‖ ≤ T)
    (hAC : 1000 ≤ A*‖c‖) :
    ‖finiteQTailSide u v c‖ ≤ (625/888 : ℝ)*T/(A^2*‖c‖^4) := by
  let U := ‖u‖
  let V := ‖v‖
  let C := ‖c‖
  let M : ℝ := 625/15984
  have hU : 0 < U := hA.trans_le hAu
  have hT : 0 < T := hU.trans_le huT
  have hV : 0 ≤ V := norm_nonneg v
  have hC : 0 < C := by
    by_contra h
    have hzero : C = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg c)
    change 1000 ≤ A*C at hAC
    rw [hzero, mul_zero] at hAC
    norm_num at hAC
  have hUC : 1000 ≤ U*C := hAC.trans
    (mul_le_mul_of_nonneg_right hAu hC.le)
  have hz : ‖1/(u*c)‖ ≤ (1/1000 : ℝ) := by
    rw [norm_div, norm_one, norm_mul]
    apply (div_le_div_iff₀ (mul_pos hU hC) (by norm_num : (0 : ℝ) < 1000)).2
    simpa using hUC
  have hrem4 := finiteQHalfRemainder_small_norm_le 4 (1/(u*c)) (by decide) hz
  have hrem5 := finiteQHalfRemainder_small_norm_le 5 (1/(u*c)) (by decide) hz
  rw [norm_div, norm_one, norm_mul] at hrem4 hrem5
  have hw0 : ‖u*(u^2-5*u*v)‖ ≤ U^3+5*U^2*V := by
    rw [norm_mul]
    calc
      _ ≤ ‖u‖*(‖u^2‖+‖5*u*v‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ = _ := by dsimp [U, V]; norm_num [norm_mul, norm_pow]; ring
  have hw1 : ‖u*(4*u^3-8*u^2*v)*c‖ ≤ (4*U^4+8*U^3*V)*C := by
    simp only [norm_mul]
    calc
      _ ≤ (‖u‖*(‖4*u^3‖+‖8*u^2*v‖))*‖c‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by
        dsimp [U, V, C]
        simp only [norm_mul, norm_pow, Complex.norm_ofNat]
        ring
  have ht0 : ‖u*(u^2-5*u*v)*finiteQHalfRemainder 4 (1/(u*c))‖ ≤
      (U^3+5*U^2*V)*(M*(1/(U*C))^4) := by
    rw [norm_mul]
    exact mul_le_mul hw0 hrem4 (norm_nonneg _) (by positivity)
  have ht1 : ‖u*(4*u^3-8*u^2*v)*c*finiteQHalfRemainder 5 (1/(u*c))‖ ≤
      ((4*U^4+8*U^3*V)*C)*(M*(1/(U*C))^5) := by
    rw [norm_mul]
    exact mul_le_mul hw1 hrem5 (norm_nonneg _) (by positivity)
  have hAT : A ≤ T := hAu.trans huT
  have hmono0 : 1/U ≤ T/A^2 := by
    apply (div_le_div_iff₀ hU (pow_pos hA 2)).2
    have hm := mul_le_mul hAT hAu hA.le hT.le
    nlinarith only [hm]
  have hmono1 : V/U^2 ≤ T/A^2 := by
    apply (div_le_div_iff₀ (pow_pos hU 2) (pow_pos hA 2)).2
    exact mul_le_mul hvT (pow_le_pow_left₀ hA.le hAu 2) (sq_nonneg A) hT.le
  calc
    _ ≤ ‖u*(u^2-5*u*v)*finiteQHalfRemainder 4 (1/(u*c))‖ +
        ‖u*(4*u^3-8*u^2*v)*c*finiteQHalfRemainder 5 (1/(u*c))‖ := norm_add_le _ _
    _ ≤ (U^3+5*U^2*V)*(M*(1/(U*C))^4) +
        ((4*U^4+8*U^3*V)*C)*(M*(1/(U*C))^5) := add_le_add ht0 ht1
    _ = M*(5*(1/U)+13*(V/U^2))/C^4 := by
      field_simp [hU.ne', hC.ne']
      <;> ring
    _ ≤ M*(5*(T/A^2)+13*(T/A^2))/C^4 := by
      dsimp [M]
      gcongr
    _ = (625/888 : ℝ)*T/(A^2*‖c‖^4) := by
      dsimp [M, C]
      ring



end D1Bound5
end
