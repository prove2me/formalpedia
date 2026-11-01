-- Prove2me | solution 1 for Erdos970.I9Bound_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:20:27.290208+00:00
-- url     : https://prove2.me/submissions/cbf3a9a8-65f4-4206-987b-0738d7ecfad2

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J000
import Theorems.Thm_Erdos970_I1Bound_jd

section
-- module Solutions.OAIQ083_JD.Erdos970_ZetaConj
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

open scoped _root_.Complex ComplexConjugate

theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.Erdos970_PNT5_Strong
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

lemma MellinTransform_integral (f : ℝ → ℂ) (s : ℂ) :
    MellinTransform f s = ∫ x in Set.Ioi (0 : ℝ), f x * (x : ℂ) ^ (s - 1) := by
  simp only [MellinTransform, mellin, smul_eq_mul, mul_comm]

open ComplexConjugate

lemma smoothedChebyshevIntegrand_conj {SmoothingF : ℝ → ℝ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
    SmoothedChebyshevIntegrand SmoothingF ε X (conj s) = conj (SmoothedChebyshevIntegrand SmoothingF ε X s) := by
  unfold SmoothedChebyshevIntegrand
  simp only [map_mul, map_div₀, map_neg]
  congr
  · exact deriv_riemannZeta_conj s
  · exact riemannZeta_conj s
  · simp_rw [MellinTransform_integral]

    rw[← integral_conj]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x xpos
    simp only [map_mul, Complex.conj_ofReal]
    congr
    nth_rw 1 [← map_one conj]
    rw[← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg xpos.le]
    exact Real.pi_ne_zero.symm
  · rw[Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg Xpos.le]
    exact Real.pi_ne_zero.symm

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

lemma I9I1 {SmoothingF : ℝ → ℝ} {ε X T : ℝ} (Xpos : 0 < X) :
    I₉ SmoothingF ε X T = conj (I₁ SmoothingF ε X T) := by
  unfold I₉ I₁
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun <| measurableSet_Ioi
    intro t ht
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp

theorem I9Bound_jd_oai
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀{ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by
  obtain ⟨C, Cpos, bound⟩ := I1Bound_jd suppSmoothingF ContDiffSmoothingF SmoothingFnonneg mass_one
  refine ⟨C, Cpos, ?_⟩
  intro ε εpos ε_lt_one X X_gt T T_gt
  specialize bound ε εpos ε_lt_one X X_gt T_gt
  rwa [I9I1 (by linarith), norm_conj]

open _root_.Filter Topology

end Erdos970
end

theorem solution : type_of% @Erdos970.I9Bound_jd_oai := @Erdos970.I9Bound_jd_oai
