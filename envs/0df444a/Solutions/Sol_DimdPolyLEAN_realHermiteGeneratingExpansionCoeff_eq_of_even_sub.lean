-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_of_even_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:02.559083+00:00
-- url     : https://prove2.me/submissions/e81ad03e-3834-4b7c-8047-6a79fb404259

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
private theorem deriv_cexp_neg_sq_div_two :
    deriv (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) =
      fun u : ℂ => -u * Complex.exp (-(u ^ (2 : ℕ)) / 2) := by
  funext u
  rw [deriv_cexp]
  · have hpoly : deriv (fun y : ℂ => -y ^ (2 : ℕ) / 2) u = -u := by
      rw [show (fun y : ℂ => -y ^ (2 : ℕ) / 2) =
          fun y : ℂ => (-1 / 2 : ℂ) * y ^ (2 : ℕ) by
        funext y
        ring]
      rw [deriv_const_mul]
      · rw [deriv_pow_field]
        ring
      · fun_prop
    rw [hpoly]
    ring
  · fun_prop
private theorem iteratedDeriv_cexp_neg_sq_div_two_zero_of_two_mul
    (r : ℕ) :
    iteratedDeriv (2 * r)
      (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0 =
      (-1 : ℂ) ^ r * ((2 * r - 1)‼ : ℂ) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega,
        iteratedDeriv_succ',
        deriv_cexp_neg_sq_div_two,
        iteratedDeriv_fun_mul]
      · rw [Finset.sum_eq_single (1 : ℕ)]
        · simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
            Nat.cast_one, iteratedDeriv_one, deriv_neg'', mul_neg, mul_one, neg_add_rev,
            add_tsub_cancel_right, ih]
          rw [Nat.doubleFactorial_add_one (2 * r)]
          norm_num
          ring
        · intro b hb hbne
          have hb_ne_one : b ≠ 1 := by omega
          have hder : iteratedDeriv b (fun u : ℂ => -u) 0 = 0 := by
            rw [show (fun u : ℂ => -u) = fun u : ℂ => (-1 : ℂ) * u by
              simp_all only [Finset.mem_range, Order.lt_add_one_iff, ne_eq, not_false_eq_true,
                neg_mul, one_mul]]
            rw [iteratedDeriv_const_mul_field]
            simp [iteratedDeriv_fun_id_zero, hb_ne_one]
          simp_all only [Finset.mem_range, Order.lt_add_one_iff, ne_eq, not_false_eq_true, mul_zero,
            zero_mul]
        · simp_all only [Finset.mem_range, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
            not_true_eq_false, Nat.choose_one_right, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
            Nat.cast_one, iteratedDeriv_one, deriv_neg'', mul_neg, mul_one, neg_add_rev,
            add_tsub_cancel_right, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq,
            true_and, Nat.cast_eq_zero, IsEmpty.forall_iff]
      · fun_prop
      · fun_prop
private theorem iteratedDeriv_cexp_neg_sq_div_two_zero_of_even
    {n : ℕ} (heven : Even n) :
    iteratedDeriv n (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0 =
      (-1 : ℂ) ^ (n / 2) * ((n - 1)‼ : ℂ) := by
  rcases heven with ⟨r, hr⟩
  rw [hr, show r + r = 2 * r by ring]
  simpa [Nat.mul_div_right _ (by norm_num : 0 < 2)]
    using iteratedDeriv_cexp_neg_sq_div_two_zero_of_two_mul r
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {n k : ℕ} (heven : Even (n - k)) :
    realHermiteGeneratingExpansionCoeff n k =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          ((-1 : ℂ) ^ ((n - k) / 2) *
            (((n - k) - 1)‼ : ℂ)))) := by
  unfold realHermiteGeneratingExpansionCoeff
  rw [iteratedDeriv_cexp_neg_sq_div_two_zero_of_even heven]
end DimdPolyLEAN
