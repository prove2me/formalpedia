-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_inner_finite_sum_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:06.26575+00:00
-- url     : https://prove2.me/submissions/e0fbd0dc-7eca-4856-878f-87d55889a23b

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff
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
private lemma sqrtTwoC_sq : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
private lemma standardGaussianMoment_add_two (r : ℕ) :
    standardGaussianMoment (r + 2) =
      (r + 1 : ℂ) * standardGaussianMoment r := by
  unfold standardGaussianMoment
  by_cases hr : Even r
  · rcases hr with ⟨s, hs⟩
    have h2 : Even (r + 2) := by
      refine ⟨s + 1, ?_⟩
      rw [hs]
      ring
    rw [if_pos h2, if_pos ⟨s, hs⟩, show r + 2 - 1 = r + 1 by omega,
      Nat.doubleFactorial_add_one]
    norm_num
  · have hodd : Odd r := Nat.not_even_iff_odd.mp hr
    rcases hodd with ⟨s, hs⟩
    have h2odd : Odd (r + 2) := by
      refine ⟨s + 1, ?_⟩
      rw [hs]
      ring
    simp_all only [Nat.not_even_bit1, not_false_eq_true, Nat.add_one_sub_one,
      Nat.doubleFactorial.eq_3, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      ↓reduceIte, mul_zero, ite_eq_right_iff, mul_eq_zero, Nat.cast_eq_zero, isEmpty_Prop,
      Nat.not_even_iff_odd, IsEmpty.forall_iff]
private lemma standardGaussianMoment_succ_eq_mul_pred (k : ℕ) :
    standardGaussianMoment (k + 1) =
      (k : ℂ) * standardGaussianMoment (k - 1) := by
  cases k with
  | zero => simp [standardGaussianMoment]
  | succ n =>
      simpa [Nat.succ_eq_add_one, add_assoc]
        using standardGaussianMoment_add_two n
private lemma realHermiteCoeffScale_sq_mul_sqrt_pi :
    (realHermiteCoeffScale * realHermiteCoeffScale) *
        (Real.sqrt Real.pi : ℂ) = 1 := by
  unfold realHermiteCoeffScale
  have hA2 :
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
          ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) =
        ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_add Real.pi_pos]
    norm_num
  rw [hA2, ← Complex.ofReal_mul]
  change ((Real.pi ^ (-(1 / 2 : ℝ)) * Real.sqrt Real.pi : ℝ) : ℂ) =
    (1 : ℂ)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
  norm_num
private lemma scaled_gamma_moment_eq_standard (r : ℕ) :
    (realHermiteCoeffScale * realHermiteCoeffScale) *
        (Real.sqrt 2 : ℂ) ^ r *
      (if Even r then (Real.Gamma ((((r : ℕ) : ℝ) + 1) / 2) : ℂ) else 0) =
      standardGaussianMoment r := by
  unfold standardGaussianMoment
  by_cases hr : Even r
  · rcases hr with ⟨s, hs⟩
    rw [if_pos ⟨s, hs⟩, if_pos ⟨s, hs⟩, hs, show s + s = 2 * s by ring]
    rw [show ((((2 * s : ℕ) : ℝ) + 1) / 2) = (s : ℝ) + 1 / 2 by
      norm_num
      ring]
    rw [Real.Gamma_nat_add_half]
    have hsqrt2pow : (Real.sqrt 2 : ℂ) ^ (2 * s) = (2 : ℂ) ^ s := by
      rw [show (Real.sqrt 2 : ℂ) ^ (2 * s) =
          ((Real.sqrt 2 : ℂ) ^ 2) ^ s by rw [pow_mul]]
      rw [sqrtTwoC_sq]
    rw [hsqrt2pow]
    have hcancel :
        (2 : ℂ) ^ s *
          ((((((2 * s - 1 : ℕ)‼ : ℕ) : ℝ) * Real.sqrt Real.pi /
                  2 ^ s : ℝ) : ℂ)) =
        (((2 * s - 1 : ℕ)‼ : ℕ) : ℂ) *
          (Real.sqrt Real.pi : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_mul]
      norm_num
      field_simp
    rw [mul_assoc, hcancel]
    calc
      realHermiteCoeffScale * realHermiteCoeffScale *
          ((((2 * s - 1 : ℕ)‼ : ℕ) : ℂ) *
            (Real.sqrt Real.pi : ℂ)) =
          (((2 * s - 1 : ℕ)‼ : ℕ) : ℂ) *
            ((realHermiteCoeffScale * realHermiteCoeffScale) *
              (Real.sqrt Real.pi : ℂ)) := by ring
      _ = (((2 * s - 1 : ℕ)‼ : ℕ) : ℂ) := by
            rw [realHermiteCoeffScale_sq_mul_sqrt_pi]
            ring
  · rw [if_neg hr, if_neg hr]
    ring
private lemma gaussianMomentFunctional_add (p q : Polynomial ℤ) :
    gaussianMomentFunctional (p + q) =
      gaussianMomentFunctional p + gaussianMomentFunctional q := by
  unfold gaussianMomentFunctional
  rw [Polynomial.sum_add_index]
  · simp only [Int.cast_zero, zero_mul, implies_true]
  · intro i a b
    norm_num
    ring
private lemma gaussianMomentFunctional_monomial (k : ℕ) (a : ℤ) :
    gaussianMomentFunctional (Polynomial.monomial k a) =
      (a : ℂ) * standardGaussianMoment k := by
  unfold gaussianMomentFunctional
  simp only [Int.cast_zero, zero_mul, Polynomial.sum_monomial_index]
private lemma gaussianMomentFunctional_neg (p : Polynomial ℤ) :
    gaussianMomentFunctional (-p) = -gaussianMomentFunctional p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [neg_add, gaussianMomentFunctional_add, gaussianMomentFunctional_add, hp, hq,
        neg_add]
  | monomial k a =>
      rw [← Polynomial.monomial_neg, gaussianMomentFunctional_monomial,
        gaussianMomentFunctional_monomial]
      simp only [Int.cast_neg, neg_mul]
private lemma gaussianMomentFunctional_sub (p q : Polynomial ℤ) :
    gaussianMomentFunctional (p - q) =
      gaussianMomentFunctional p - gaussianMomentFunctional q := by
  rw [sub_eq_add_neg, gaussianMomentFunctional_add, gaussianMomentFunctional_neg]
  ring
private lemma gaussianMomentFunctional_smul_int (c : ℤ) (p : Polynomial ℤ) :
    gaussianMomentFunctional (c • p) =
      (c : ℂ) * gaussianMomentFunctional p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show c • (p + q) = c • p + c • q from smul_add c p q,
        gaussianMomentFunctional_add, gaussianMomentFunctional_add, hp, hq, mul_add]
  | monomial k a =>
      rw [show c • Polynomial.monomial k a = Polynomial.monomial k (c • a) from
          Polynomial.smul_monomial c k a]
      rw [gaussianMomentFunctional_monomial, gaussianMomentFunctional_monomial, smul_eq_mul]
      push_cast
      ring
private lemma gaussianMomentFunctional_finset_sum
    {α : Type*} (s : Finset α) (f : α → Polynomial ℤ) :
    gaussianMomentFunctional (∑ x ∈ s, f x) =
      ∑ x ∈ s, gaussianMomentFunctional (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussianMomentFunctional]
  | insert a s ha ih =>
      simp [ha, gaussianMomentFunctional_add, ih]
private lemma gaussianMomentFunctional_polynomial_sum
    (p : Polynomial ℤ) (f : ℕ → ℤ → Polynomial ℤ) :
    gaussianMomentFunctional (p.sum f) =
      p.sum fun k a => gaussianMomentFunctional (f k a) := by
  rw [Polynomial.sum_def, gaussianMomentFunctional_finset_sum]
  rfl
private lemma gaussianMomentFunctional_mul (p q : Polynomial ℤ) :
    gaussianMomentFunctional (p * q) = gaussianMomentBilinear p q := by
  rw [Polynomial.mul_eq_sum_sum, gaussianMomentFunctional_finset_sum]
  unfold gaussianMomentBilinear
  apply Finset.sum_congr rfl
  intro i hi
  rw [gaussianMomentFunctional_polynomial_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [gaussianMomentFunctional_monomial]
private lemma gaussianMomentFunctional_X_mul_eq_derivative
    (p : Polynomial ℤ) :
    gaussianMomentFunctional (Polynomial.X * p) =
      gaussianMomentFunctional (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [mul_add, Polynomial.derivative_add, gaussianMomentFunctional_add,
        gaussianMomentFunctional_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.X_mul_monomial, Polynomial.derivative_monomial,
        gaussianMomentFunctional_monomial, gaussianMomentFunctional_monomial,
        standardGaussianMoment_succ_eq_mul_pred]
      norm_num
      ring
private lemma derivative_hermite_int (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite n) =
      (n : ℤ) • Polynomial.hermite (n - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          cases n with
          | zero => simp
          | succ n =>
              have ih_succ :
                  Polynomial.derivative (Polynomial.hermite (n + 1)) =
                    ((n + 1 : ℕ) : ℤ) •
                      Polynomial.hermite ((n + 1) - 1) :=
                ih (n + 1) (by omega)
              have ih_n :
                  Polynomial.derivative (Polynomial.hermite n) =
                    (n : ℤ) • Polynomial.hermite (n - 1) :=
                ih n (by omega)
              rw [Polynomial.hermite_succ, Polynomial.derivative_sub,
                Polynomial.derivative_mul, Polynomial.derivative_X, ih_succ]
              rw [show (n + 1 - 1 : ℕ) = n by omega,
                map_zsmul Polynomial.derivative, ih_n,
                show (n + 1 + 1 - 1 : ℕ) = n + 1 by omega,
                Polynomial.hermite_succ,
                ih_n]
              norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
              ring
private lemma derivative_hermite_succ_int (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite (n + 1)) =
      ((n + 1 : ℕ) : ℤ) • Polynomial.hermite n := by exact derivative_hermite_int (n + 1)
private lemma hermiteStandardInner_comm (n m : ℕ) :
    hermiteStandardInner n m = hermiteStandardInner m n := by
  unfold hermiteStandardInner
  rw [mul_comm]
private lemma hermiteStandardInner_zero_zero : hermiteStandardInner 0 0 = 1 := by
  unfold hermiteStandardInner
  simp only [Polynomial.hermite_zero]
  rw [show Polynomial.C (1 : ℤ) * Polynomial.C (1 : ℤ) =
      Polynomial.C (1 : ℤ) by norm_num]
  unfold gaussianMomentFunctional standardGaussianMoment
  rw [Polynomial.sum_C_index]
  · norm_num
  · simp
private lemma hermiteStandardInner_succ_zero (n : ℕ) :
    hermiteStandardInner (n + 1) 0 = 0 := by
  unfold hermiteStandardInner
  simp only [Polynomial.hermite_zero]
  rw [show Polynomial.hermite (n + 1) * Polynomial.C (1 : ℤ) =
      Polynomial.hermite (n + 1) by norm_num]
  rw [Polynomial.hermite_succ,
    gaussianMomentFunctional_sub,
    gaussianMomentFunctional_X_mul_eq_derivative]
  simp
private lemma hermiteStandardInner_zero_succ (m : ℕ) :
    hermiteStandardInner 0 (m + 1) = 0 := by
  rw [hermiteStandardInner_comm]
  exact hermiteStandardInner_succ_zero m
private lemma hermiteStandardInner_succ_succ (n m : ℕ) :
    hermiteStandardInner (n + 1) (m + 1) =
      ((m + 1 : ℕ) : ℂ) * hermiteStandardInner n m := by
  unfold hermiteStandardInner
  rw [Polynomial.hermite_succ n, sub_mul, gaussianMomentFunctional_sub]
  have hX :
      gaussianMomentFunctional
          ((Polynomial.X * Polynomial.hermite n) *
            Polynomial.hermite (m + 1)) =
        gaussianMomentFunctional
          (Polynomial.derivative
            (Polynomial.hermite n * Polynomial.hermite (m + 1))) := by
    rw [mul_assoc]
    exact gaussianMomentFunctional_X_mul_eq_derivative _
  rw [hX,
    Polynomial.derivative_mul,
    gaussianMomentFunctional_add,
    sub_eq_iff_eq_add,
    derivative_hermite_succ_int,
    mul_smul_comm,
    gaussianMomentFunctional_smul_int]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring
private theorem hermiteStandardInner_eq_factorial (n m : ℕ) :
    hermiteStandardInner n m =
      if n = m then (Nat.factorial n : ℂ) else 0 := by
  induction n generalizing m with
  | zero =>
      cases m with
      | zero => simp [hermiteStandardInner_zero_zero]
      | succ m => simp [hermiteStandardInner_zero_succ]
  | succ n ih =>
      cases m with
      | zero => simp [hermiteStandardInner_succ_zero]
      | succ m =>
          rw [hermiteStandardInner_succ_succ, ih m]
          by_cases h : n = m
          · subst m
            simp [Nat.factorial_succ]
          · simp_all only [Nat.cast_add, Nat.cast_one, ↓reduceIte, mul_zero,
              Nat.add_right_cancel_iff]
private lemma hermite_support_subset_range_succ (n : ℕ) :
    (Polynomial.hermite n).support ⊆ Finset.range (n + 1) := by
  intro k hk
  rw [Finset.mem_range]
  by_contra h
  have hlt : n < k := by omega
  exact (Polynomial.mem_support_iff.mp hk)
    (Polynomial.coeff_hermite_of_lt hlt)
private lemma gaussianMomentBilinear_hermite_eq_finite_sum
    (n m : ℕ) :
    gaussianMomentBilinear (Polynomial.hermite n) (Polynomial.hermite m) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        ((Polynomial.hermite n).coeff k : ℂ) *
          ((Polynomial.hermite m).coeff l : ℂ) *
            standardGaussianMoment (k + l) := by
  unfold gaussianMomentBilinear
  rw [Polynomial.sum_eq_of_subset
    (p := Polynomial.hermite n)
    (f := fun k a =>
      (Polynomial.hermite m).sum fun l b =>
        (a : ℂ) * (b : ℂ) * standardGaussianMoment (k + l))
    (hf := by intro i; simp [Polynomial.sum_def])
    (s := Finset.range (n + 1))
    (hs := hermite_support_subset_range_succ n)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.sum_eq_of_subset
    (p := Polynomial.hermite m)
    (f := fun l b =>
      ((Polynomial.hermite n).coeff k : ℂ) * (b : ℂ) *
        standardGaussianMoment (k + l))
    (hf := by intro i; simp)
    (s := Finset.range (m + 1))
    (hs := hermite_support_subset_range_succ m)]
private lemma hermiteStandardInner_eq_finite_sum (n m : ℕ) :
    hermiteStandardInner n m =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        ((Polynomial.hermite n).coeff k : ℂ) *
          ((Polynomial.hermite m).coeff l : ℂ) *
            standardGaussianMoment (k + l) := by
  unfold hermiteStandardInner
  rw [gaussianMomentFunctional_mul]
  exact gaussianMomentBilinear_hermite_eq_finite_sum n m
private lemma realHermiteGeneratingExpansionCoeff_eq_scale_coeff
    (n k : ℕ) :
    realHermiteGeneratingExpansionCoeff n k =
      realHermiteCoeffScale *
        ((Real.sqrt 2 : ℂ) ^ k * ((Polynomial.hermite n).coeff k : ℂ)) := by
  simpa [realHermiteCoeffScale]
    using realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff n k
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
    (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (if Even (k + l) then
            (Real.Gamma ((((k + l : ℕ) : ℝ) + 1) / 2) : ℂ)
          else 0)) =
      if n = m then (Nat.factorial n : ℂ) else 0 := by
  rw [← hermiteStandardInner_eq_factorial n m, hermiteStandardInner_eq_finite_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [realHermiteGeneratingExpansionCoeff_eq_scale_coeff,
    realHermiteGeneratingExpansionCoeff_eq_scale_coeff]
  rw [← scaled_gamma_moment_eq_standard (k + l), pow_add]
  ring
end DimdPolyLEAN
