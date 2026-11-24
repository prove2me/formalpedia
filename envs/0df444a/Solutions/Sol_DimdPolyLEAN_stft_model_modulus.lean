-- Prove2me | solution 1 for DimdPolyLEAN.stft_model_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:15.767598+00:00
-- url     : https://prove2.me/submissions/7ef70f13-41ca-4b35-90a4-6fab1a75d5c5

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_stft_integral_kernel
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_ambiguity_integral_independent_kernel
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_expansion_monomial
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_star
public import Theorems.Thm_DimdPolyLEAN_realHermiteTensorL2_orthonormal
public import Theorems.Thm_DimdPolyLEAN_varphiKappa_coe_ae_eq_realHermiteTensorRep
public import Theorems.Thm_DimdPolyLEAN_summable_realHermiteTensorL2_coeff_smul_of_orthonormal
public import Theorems.Thm_DimdPolyLEAN_WKappa_pos
public import Theorems.Thm_DimdPolyLEAN_stftRep_eq_lpPairing
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
private lemma sqrtTwoC_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
private theorem iteratedDeriv_cexp_affine_at_zero (n : ℕ) (a b : ℂ) :
    iteratedDeriv n (fun u : ℂ => Complex.exp (a * u + b)) 0 =
      a ^ n * Complex.exp b := by
  rw [show (fun u : ℂ => Complex.exp (a * u + b)) =
      fun u : ℂ => Complex.exp b * Complex.exp (a * u) by
    funext u
    rw [Complex.exp_add]
    ring]
  rw [iteratedDeriv_const_mul_field]
  simp [iteratedDeriv_cexp_const_mul, mul_comm]
private theorem iteratedDeriv_shifted_pow_at_zero (n k : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ => (w + z) ^ k) 0 =
      (k.descFactorial n : ℂ) * z ^ (k - n) := by
  rw [show (fun w : ℂ => (w + z) ^ k) = fun w : ℂ => (fun y : ℂ => y ^ k) (w + z) by rfl]
  have h := congrFun (iteratedDeriv_comp_add_const n (fun y : ℂ => y ^ k) z) 0
  simpa [Nat.cast_mul] using h
private theorem iteratedDeriv_cexp_ambiguity_kernel_u_at_zero
    (k : ℕ) (z w : ℂ) :
    iteratedDeriv k
      (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0 =
      (w + z) ^ k * Complex.exp (-(star z) * w) := by
  rw [show (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) =
      fun u : ℂ => Complex.exp ((w + z) * u + (-(star z) * w)) by
    funext u
    congr 1
    ring]
  rw [iteratedDeriv_cexp_affine_at_zero]
private theorem iteratedDeriv_cexp_ambiguity_kernel_at_zero_sum
    (n k : ℕ) (z : ℂ) :
    iteratedDeriv k
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) *
          (((n.descFactorial i : ℕ) : ℂ) * z ^ (n - i)) *
            (-(star z)) ^ (k - i) := by
  rw [show
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) =
      fun w : ℂ => (w + z) ^ n * Complex.exp (-(star z) * w) by
    funext w
    exact iteratedDeriv_cexp_ambiguity_kernel_u_at_zero n z w]
  rw [iteratedDeriv_fun_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_shifted_pow_at_zero, iteratedDeriv_cexp_const_mul]
    simp [mul_assoc]
  · fun_prop
  · fun_prop
private theorem neg_one_pow_mul_of_le (k i : ℕ) (hi : i ≤ k) :
    ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ i) = (-1 : ℂ) ^ (k - i) := by
  calc
    ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ i) =
        (-1 : ℂ) ^ (k + i) := by rw [← pow_add]
    _ = (-1 : ℂ) ^ ((k - i) + 2 * i) := by
        congr 1
        omega
    _ = (-1 : ℂ) ^ (k - i) * ((-1 : ℂ) ^ 2) ^ i := by rw [pow_add, pow_mul]
    _ = (-1 : ℂ) ^ (k - i) := by norm_num
private theorem cexp_ambiguity_kernel_sum_eq_complexHermite
    (n k : ℕ) (z : ℂ) :
    (∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) *
          (((n.descFactorial i : ℕ) : ℂ) * z ^ (n - i)) *
            (-(star z)) ^ (k - i)) =
      (-1 : ℂ) ^ k * complexHermite n k z := by
  rw [complexHermite, Finset.mul_sum]
  have hsubset : Finset.range (min n k + 1) ⊆ Finset.range (k + 1) := by
    simp_all only [Finset.range_subset_range, add_le_add_iff_right, min_le_iff, Std.le_refl,
      or_true]
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi_le_min : i ≤ min n k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi_le_n : i ≤ n := hi_le_min.trans (Nat.min_le_left n k)
    have hi_le_k : i ≤ k := hi_le_min.trans (Nat.min_le_right n k)
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    rw [show (-(star z)) ^ (k - i) =
        (-1 : ℂ) ^ (k - i) * (star z) ^ (k - i) by
      rw [neg_eq_neg_one_mul, mul_pow]]
    rw [← neg_one_pow_mul_of_le k i hi_le_k]
    norm_num [Nat.cast_mul]
    ring
  · simp_all only [Finset.range_subset_range, add_le_add_iff_right, min_le_iff, Std.le_refl,
      or_true, Finset.mem_range, Order.lt_add_one_iff, le_inf_iff, and_true, not_le,
      RCLike.star_def, mul_eq_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt,
      pow_eq_zero_iff', ne_eq, true_or, neg_eq_zero, map_eq_zero, implies_true]
private theorem iteratedDeriv_cexp_ambiguity_kernel_at_zero
    (n k : ℕ) (z : ℂ) :
    iteratedDeriv k
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 =
      (-1 : ℂ) ^ k * complexHermite n k z := by
  rw [iteratedDeriv_cexp_ambiguity_kernel_at_zero_sum]
  exact cexp_ambiguity_kernel_sum_eq_complexHermite n k z
private theorem realHermiteGenerating_stft_integral_eq_phase_mul_halfCentered
    (n k : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ))) *
        (∫ t : ℝ,
          iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
            iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ ω t : ℝ) : ℂ))) := by
  let F : ℝ → ℂ := fun t =>
    iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
      iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ))
  let G : ℝ → ℂ := fun t =>
    iteratedDeriv n (realHermiteGenerating t) 0 *
      iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ω t : ℝ) : ℂ))
  let phase : ℂ := Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ)))
  let phaseInv : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ)))
  have hshift :
      (∫ t : ℝ, F t) =
        ∫ t : ℝ, F (t + (-(1 / 2 : ℝ) * x)) := by
    exact
      (MeasureTheory.integral_add_right_eq_self
        (μ := volume) F (-(1 / 2 : ℝ) * x)).symm
  have hshift_eval :
      (∫ t : ℝ, F (t + (-(1 / 2 : ℝ) * x))) =
        phaseInv * ∫ t : ℝ, G t := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    dsimp [F, G, phaseInv]
    have htplus : t + -(1 / 2 : ℝ) * x + (1 / 2 : ℝ) * x = t := by ring
    have htminus : t + -(1 / 2 : ℝ) * x - (1 / 2 : ℝ) * x = t - x := by ring
    rw [htplus, htminus]
    rw [show
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            (((t + -(1 / 2 : ℝ) * x) * (starRingEnd ℝ) ω : ℝ) : ℂ)) =
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ))) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((t * (starRingEnd ℝ) ω : ℝ) : ℂ)) by
      rw [← Complex.exp_add]
      congr 1
      simp
      ring_nf]
    ring
  have hF : (∫ t : ℝ, F t) = phaseInv * ∫ t : ℝ, G t := by rw [hshift, hshift_eval]
  have hphase : phase * phaseInv = 1 := by
    dsimp [phase, phaseInv]
    rw [← Complex.exp_add]
    simp_all only [one_div, neg_mul, neg_add_cancel, Complex.exp_zero]
  change (∫ t : ℝ, G t) = phase * (∫ t : ℝ, F t)
  rw [hF, ← mul_assoc, hphase, one_mul]
private lemma ambiguity_kernel_iteratedDeriv_factor (n : ℕ) (x ω : ℝ) :
    (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            ∫ t : ℝ,
              realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                    ((inner ℝ ω t : ℝ) : ℂ))) 0) =
      fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp
              (u * w +
                  ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ) * u -
                star
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                      (Real.sqrt 2 : ℂ)) * w)) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  funext w
  rw [show
      (fun u : ℂ =>
        ∫ t : ℝ,
          realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
            realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ ω t : ℝ) : ℂ))) =
        fun u : ℂ =>
          Complex.exp
            (u * w +
                ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                    (Real.sqrt 2 : ℂ) * u -
              star
                  (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                    (Real.sqrt 2 : ℂ)) * w) *
            Complex.ofReal
              (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) by
      funext u
      simpa [inner, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using realHermiteGenerating_ambiguity_integral_independent_kernel x ω u w]
  rw [iteratedDeriv_mul_const_field]
private theorem realHermiteGenerating_stft_interchange_of_halfCentered_interchange
    (n k : ℕ) (x ω : ℝ)
    (hhalf :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                    realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating t) 0 *
        iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      iteratedDeriv k
        (fun v : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating t u *
                  realHermiteGenerating (t - x) v *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  let phase : ℂ := Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ)))
  have hleft :=
    realHermiteGenerating_stft_integral_eq_phase_mul_halfCentered n k x ω
  have hhalfKernel :
      iteratedDeriv k
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                  realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 =
        ((-1 : ℂ) ^ k * complexHermite n k z) * E := by
    show iteratedDeriv k
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                  realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 = _
    rw [ambiguity_kernel_iteratedDeriv_factor n x ω, iteratedDeriv_mul_const_field,
      iteratedDeriv_cexp_ambiguity_kernel_at_zero]
  have hstftKernel :
      iteratedDeriv k
        (fun v : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating t u *
                  realHermiteGenerating (t - x) v *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 =
        phase * (((-1 : ℂ) ^ k * complexHermite n k z) * E) := by
    have hfun :
        (fun v : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating t u *
                    realHermiteGenerating (t - x) v *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) =
          fun v : ℂ =>
            phase *
              (iteratedDeriv n
                (fun u : ℂ => Complex.exp (u * v + z * u - star z * v)) 0 * E) := by
      funext v
      rw [show
          (fun u : ℂ =>
            ∫ t : ℝ,
              realHermiteGenerating t u *
                realHermiteGenerating (t - x) v *
                  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                    ((inner ℝ ω t : ℝ) : ℂ))) =
          fun u : ℂ =>
            phase * (Complex.exp (u * v + z * u - star z * v) * E) by
        funext u
        simpa only [Real.inner_apply, Complex.ofReal_mul] using
          (realHermiteGenerating_stft_integral_kernel x ω u v).trans (mul_assoc _ _ _)]
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field]
    rw [hfun,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_mul_const_field,
      iteratedDeriv_cexp_ambiguity_kernel_at_zero]
  rw [hleft, hhalf, hhalfKernel, hstftKernel]
private theorem realHermite1D_stft_integral_formula_of_interchange
    (n k : ℕ) (x ω : ℝ)
    (hinterchange :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating t) 0 *
          iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        iteratedDeriv k
          (fun v : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating t u *
                    realHermiteGenerating (t - x) v *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0) :
    (∫ t : ℝ,
      realHermite1D n t *
        star (realHermite1D k (t - x)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      (-1 : ℂ) ^ k *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ))) *
          (Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) *
            phi1D k n (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ))) := by
  let cn : ℂ := (Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)
  let ck : ℂ := (Real.sqrt (Nat.factorial k : ℝ) : ℂ) / (Nat.factorial k : ℂ)
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  let phase : ℂ :=
    Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ)))
  have hck_star : star ck = ck := by simp [ck, Complex.conj_ofReal]
  have hscale :
      cn * ck * complexHermite n k z = phi1D k n z := by
    let sn : ℂ := (Real.sqrt (Nat.factorial n : ℝ) : ℂ)
    let sk : ℂ := (Real.sqrt (Nat.factorial k : ℝ) : ℂ)
    let fn : ℂ := (Nat.factorial n : ℂ)
    let fk : ℂ := (Nat.factorial k : ℂ)
    have hfn_ne0 : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hfk_ne0 : (Nat.factorial k : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hfn_ne : fn ≠ 0 := by exact hfn_ne0
    have hfk_ne : fk ≠ 0 := by exact hfk_ne0
    have hfn_pos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hfk_pos : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hsn_ne0 : ((Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hfn_pos).ne'
    have hsk_ne0 : ((Real.sqrt (Nat.factorial k : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hfk_pos).ne'
    have hsn_ne : sn ≠ 0 := by exact hsn_ne0
    have hsk_ne : sk ≠ 0 := by exact hsk_ne0
    have hsn_sq : sn ^ 2 = fn := by
      norm_num [sn, fn, ← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hfn_pos)]
    have hsk_sq : sk ^ 2 = fk := by
      norm_num [sk, fk, ← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hfk_pos)]
    have hsqrt_mul :
        ((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ) =
          sn * sk := by
      rw [← Complex.ofReal_mul]
      simp_all only [neg_mul, RCLike.inner_apply, conj_trivial, Complex.ofReal_mul, RCLike.star_def,
        ne_eq, Nat.cast_eq_zero, Nat.cast_pos, Complex.ofReal_eq_zero, Nat.cast_nonneg,
        Real.sqrt_eq_zero, not_false_eq_true, Real.sqrt_mul]
    have hscale_scalar : cn * ck = (sn * sk)⁻¹ := by
      change (sn / fn) * (sk / fk) = (sn * sk)⁻¹
      field_simp [hfn_ne, hfk_ne, hsn_ne, hsk_ne]
      rw [← hsn_sq, ← hsk_sq]
    unfold phi1D
    rw [hsqrt_mul, hscale_scalar]
  have hscaled_integral :
      (∫ t : ℝ,
        realHermite1D n t *
          star (realHermite1D k (t - x)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        (cn * ck) *
          ∫ t : ℝ,
            iteratedDeriv n (realHermiteGenerating t) 0 *
              iteratedDeriv k (realHermiteGenerating (t - x)) 0 *
                Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                  ((inner ℝ ω t : ℝ) : ℂ)) := by
    unfold realHermite1D
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [star_mul, hck_star, realHermiteGenerating_iteratedDeriv_zero_star]
    ring
  have hkernel :
      iteratedDeriv k
          (fun v : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating t u *
                    realHermiteGenerating (t - x) v *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 =
        phase * (((-1 : ℂ) ^ k * complexHermite n k z) * E) := by
    have hfun :
        (fun v : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating t u *
                    realHermiteGenerating (t - x) v *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) =
          fun v : ℂ =>
            phase *
              (iteratedDeriv n
                (fun u : ℂ => Complex.exp (u * v + z * u - star z * v)) 0 * E) := by
      funext v
      rw [show
          (fun u : ℂ =>
            ∫ t : ℝ,
              realHermiteGenerating t u *
                realHermiteGenerating (t - x) v *
                  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                    ((inner ℝ ω t : ℝ) : ℂ))) =
          fun u : ℂ =>
            phase * (Complex.exp (u * v + z * u - star z * v) * E) by
        funext u
        simpa only [Real.inner_apply, Complex.ofReal_mul] using
          (realHermiteGenerating_stft_integral_kernel x ω u v).trans (mul_assoc _ _ _)]
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field]
    rw [hfun,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_mul_const_field,
      iteratedDeriv_cexp_ambiguity_kernel_at_zero]
  rw [hscaled_integral, hinterchange, hkernel]
  change (cn * ck) * (phase * (((-1 : ℂ) ^ k * complexHermite n k z) * E)) =
    (-1 : ℂ) ^ k * phase * (E * phi1D k n z)
  rw [← hscale]
  ring_nf
private theorem realHermite1D_stft_integral_formula_of_halfCentered_interchange
    (n k : ℕ) (x ω : ℝ)
    (hhalf :
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv n
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                    realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0) :
    (∫ t : ℝ,
      realHermite1D n t *
        star (realHermite1D k (t - x)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      (-1 : ℂ) ^ k *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * ((x : ℂ) * (ω : ℂ))) *
          (Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) *
            phi1D k n (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
              (Real.sqrt 2 : ℂ))) :=
  realHermite1D_stft_integral_formula_of_interchange n k x ω
    (realHermiteGenerating_stft_interchange_of_halfCentered_interchange n k x ω hhalf)
private theorem stftModelPhase_norm {d : Nat} (kappa : MultiIndex d)
    (ξ : PhaseSpace d) :
    ‖stftModelPhase kappa ξ‖ = 1 := by
  unfold stftModelPhase
  rw [norm_mul]
  have hpow :
      ‖((-1 : ℂ) ^
          ((Finset.univ : Finset (Fin d)).sum fun q => kappa q))‖ = 1 := by simp
  have hexp :
      ‖Complex.exp (-(Real.pi : ℂ) * Complex.I *
          ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp_all only [norm_pow, norm_neg, norm_one, one_pow, neg_mul, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      zero_mul, Complex.mul_im, add_zero, neg_zero, Real.exp_zero]
  simp_all only [norm_pow, norm_neg, norm_one, one_pow, neg_mul, mul_one]
private theorem stftRep_varphiKappa_realHermiteTensorL2_eq_tensorRep_integral
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    stftRep (varphiKappa kappa) (realHermiteTensorL2 alpha) ξ =
      ∫ t : RealVec d,
        realHermiteTensorRep alpha t *
          star (realHermiteTensorRep kappa (t - ξ.1)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ)) := by
  unfold stftRep
  apply MeasureTheory.integral_congr_ae
  have hsig :
      ((realHermiteTensorL2 alpha : L2Real d) : RealVec d -> ℂ)
        =ᵐ[(volume : Measure (RealVec d))] realHermiteTensorRep alpha := by
    simpa [realHermiteTensorL2] using varphiKappa_coe_ae_eq_realHermiteTensorRep alpha
  have hwin :
      (fun t : RealVec d =>
        ((varphiKappa kappa : L2Real d) : RealVec d -> ℂ) (t - ξ.1))
        =ᵐ[(volume : Measure (RealVec d))]
          fun t : RealVec d => realHermiteTensorRep kappa (t - ξ.1) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      ((MeasureTheory.measurePreserving_add_right
        (volume : Measure (RealVec d))
        (-ξ.1)).quasiMeasurePreserving).ae_eq_comp
          (varphiKappa_coe_ae_eq_realHermiteTensorRep kappa)
  filter_upwards [hsig, hwin] with t hsig_t hwin_t
  rw [hsig_t, hwin_t]
private theorem tensorRep_stft_integral_eq_prod_oneD
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    (∫ t : RealVec d,
      realHermiteTensorRep alpha t *
        star (realHermiteTensorRep kappa (t - ξ.1)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      ∏ q : Fin d,
        ∫ s : ℝ,
          realHermite1D (alpha q) s *
            star (realHermite1D (kappa q) (s - ξ.1 q)) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ (ξ.2 q) s : ℝ) : ℂ)) := by
  classical
  let f : (q : Fin d) → ℝ → ℂ := fun q s =>
    realHermite1D (alpha q) s *
      star (realHermite1D (kappa q) (s - ξ.1 q)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ (ξ.2 q) s : ℝ) : ℂ))
  have h_real_to_pi :
      (∫ t : RealVec d,
        realHermiteTensorRep alpha t *
          star (realHermiteTensorRep kappa (t - ξ.1)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
        ∫ y : Fin d → ℝ, ∏ q : Fin d, f q (y q) := by
    calc
      (∫ t : RealVec d,
        realHermiteTensorRep alpha t *
          star (realHermiteTensorRep kappa (t - ξ.1)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
          ∫ t : RealVec d,
            (fun y : Fin d → ℝ => ∏ q : Fin d, f q (y q)) (WithLp.ofLp t) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with t
            simp only [f, realHermiteTensorRep, Finset.prod_mul_distrib]
            rw [star_prod]
            have hphase :
                Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                    ((inner ℝ ξ.2 t : ℝ) : ℂ)) =
                  ∏ q : Fin d,
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ (ξ.2 q) (WithLp.ofLp t q) : ℝ) : ℂ)) := by
              rw [show
                  -(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ξ.2 t : ℝ) : ℂ) =
                    ∑ q : Fin d,
                      -(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ (ξ.2 q) (WithLp.ofLp t q) : ℝ) : ℂ) by
                simp only [PiLp.inner_apply, Complex.ofReal_sum, Finset.mul_sum]]
              rw [Complex.exp_sum]
            simp_all only [neg_mul, RCLike.inner_apply, conj_trivial, Complex.ofReal_mul,
              PiLp.sub_apply, RCLike.star_def]
      _ = ∫ y : Fin d → ℝ, ∏ q : Fin d, f q (y q) := by
            simpa [MeasurableEquiv.coe_toLp_symm] using
              (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
                (g := fun y : Fin d → ℝ => ∏ q : Fin d, f q (y q))
  rw [h_real_to_pi]
  exact
    MeasureTheory.integral_fintype_prod_volume_eq_prod
      (f := fun q (t : ℝ) => f q t)
private theorem prod_oneDRealHermiteSTFT_closed_eq_model
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    (∏ q : Fin d,
      (-1 : ℂ) ^ kappa q *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) *
          (Complex.ofReal
            (Real.exp (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))) *
            phi1D (kappa q) (alpha q) (TKappa ξ q))) =
      stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) *
          Phi kappa alpha (TKappa ξ)) := by
  classical
  let coordQ : Fin d → ℝ := fun q =>
    (((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4)
  have hQsum : QKappa ξ = ∑ q : Fin d, coordQ q := by
    simp only [QKappa, coordQ, EuclideanSpace.real_norm_sq_eq]
    ring_nf
    rw [Finset.sum_add_distrib]
    simp only [one_div, Finset.sum_mul]
    rw [add_comm, Finset.mul_sum]
  have hprod_pow :
      (∏ q : Fin d, (-1 : ℂ) ^ kappa q) =
        (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun q => kappa q) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin d))
        (fun q : Fin d => kappa q) (-1 : ℂ))
  have hprod_phase :
      (∏ q : Fin d,
        Complex.exp (-(Real.pi : ℂ) * Complex.I *
          (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ)))) =
        Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) := by
    calc
      (∏ q : Fin d,
        Complex.exp (-(Real.pi : ℂ) * Complex.I *
          (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ)))) =
          Complex.exp
            (∑ q : Fin d,
              -(Real.pi : ℂ) * Complex.I * (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) := by
            rw [Complex.exp_sum]
      _ = Complex.exp (-(Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) := by
            congr 1
            simp only [PiLp.inner_apply, Complex.ofReal_sum, Finset.mul_sum]
            simp [inner, mul_assoc, mul_comm]
  have hprod_exp :
      (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) =
        Complex.ofReal (Real.exp (-(QKappa ξ))) := by
    calc
      (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) =
          ∏ q : Fin d, Complex.exp (((-(coordQ q) : ℝ) : ℂ)) := by
            simp_all only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg]
      _ = Complex.exp (∑ q : Fin d, (((-(coordQ q) : ℝ) : ℂ))) := by rw [Complex.exp_sum]
      _ = Complex.ofReal (Real.exp (-(QKappa ξ))) := by
            simp_all only [neg_mul, Complex.ofReal_neg, Finset.sum_neg_distrib, Complex.ofReal_exp,
              Complex.ofReal_sum]
  calc
    (∏ q : Fin d,
      (-1 : ℂ) ^ kappa q *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) *
          (Complex.ofReal
            (Real.exp (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))) *
            phi1D (kappa q) (alpha q) (TKappa ξ q))) =
        (∏ q : Fin d, (-1 : ℂ) ^ kappa q) *
          (∏ q : Fin d,
            Complex.exp (-(Real.pi : ℂ) * Complex.I *
              (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ)))) *
            ((∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) *
              (∏ q : Fin d, phi1D (kappa q) (alpha q) (TKappa ξ q))) := by
          simp [coordQ, Finset.prod_mul_distrib, mul_assoc]
    _ = stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) * Phi kappa alpha (TKappa ξ)) := by
          rw [hprod_pow, hprod_phase, hprod_exp]
          simp [stftModelPhase, WKappa, Phi, mul_assoc]
private theorem realHermiteGenerating_pi_quarter_mul_self :
    (((Real.pi ^ (-(4 : ℝ)⁻¹) : ℝ) : ℂ) *
        ((Real.pi ^ (-(4 : ℝ)⁻¹) : ℝ) : ℂ)) =
      ((Real.pi ^ (-(2 : ℝ)⁻¹) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_add Real.pi_pos]
  norm_num
private theorem star_complex_monomial_gaussian (k : ℕ) (t : ℝ) :
    star (complexMonomialGaussian k t) = complexMonomialGaussian k t := by
  unfold complexMonomialGaussian
  rw [star_mul, star_pow]
  have ht : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  rw [ht]
  have hexp : star (Complex.exp (-(((t : ℂ) ^ 2) / 2))) =
      Complex.exp (-(((t : ℂ) ^ 2) / 2)) := by
    change (starRingEnd ℂ) (Complex.exp (-(((t : ℂ) ^ 2) / 2))) =
      Complex.exp (-(((t : ℂ) ^ 2) / 2))
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_div₀, map_pow, Complex.conj_ofReal]
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
    rw [htwo]
  rw [hexp]
  ring
private theorem gaussianPDFReal_zero_half_scalar :
    (Real.sqrt 2 : ℂ) *
        (((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) =
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hreal : Real.sqrt 2 * ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) =
      Real.pi ^ (-(1 / 2 : ℝ)) := by
    have hsqrt2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp [hsqrt2]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
    norm_num
  exact_mod_cast hreal
private theorem gaussianPDFReal_zero_half_eq (t : ℝ) :
    ((ProbabilityTheory.gaussianPDFReal 0 (1 / 2 : NNReal) t : ℝ) : ℂ) =
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-((t : ℂ) ^ 2)) := by
  unfold ProbabilityTheory.gaussianPDFReal
  norm_num
  rw [gaussianPDFReal_zero_half_scalar]
private theorem integral_gaussian_zero_half_eq_density (f : ℝ → ℂ) :
    (∫ t : ℝ, f t ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      ∫ t : ℝ, ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-((t : ℂ) ^ 2)) * f t := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (μ := (0 : ℝ)) (v := (1 / 2 : NNReal)) (f := f) (by norm_num)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  change ((ProbabilityTheory.gaussianPDFReal 0 (1 / 2 : NNReal) t : ℝ) : ℂ) *
      f t = _
  rw [gaussianPDFReal_zero_half_eq]
private theorem gaussian_half_moment_eq_iteratedDeriv (n : ℕ) (z : ℂ) :
    (∫ x : ℝ, ((x : ℂ) ^ n * Complex.exp (z * (x : ℂ)))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      iteratedDeriv n (fun z : ℂ => Complex.exp (z ^ 2 / 4)) z := by
  rw [← ProbabilityTheory.iteratedDeriv_complexMGF
    (X := fun x : ℝ => x)
    (μ := ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))
    (z := z) (n := n) (by simp)]
  congr 1
  funext y
  change ProbabilityTheory.complexMGF id
      (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) y =
    Complex.exp (y ^ 2 / 4)
  rw [ProbabilityTheory.complexMGF_id_gaussianReal
    (μ := (0 : ℝ)) (v := (1 / 2 : NNReal)) y]
  congr 1
  norm_num
  ring
private theorem gaussian_half_integrable_monomial_exp (n : ℕ) (z : ℂ) :
    Integrable (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (z * (t : ℂ)))
      (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) := by
  exact ProbabilityTheory.integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (X := fun t : ℝ => t)
    (μ := ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))
    (z := z) (by simp) n
private theorem gaussian_half_exp_factor_eq_closed_exp (x ω : ℝ) :
    Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        Complex.exp ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2 / 4) =
      Complex.ofReal (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  norm_num [← Complex.ofReal_pow]
  ring_nf
  rw [Complex.I_sq]
  norm_num [← Complex.ofReal_pow]
  ring_nf
private theorem shifted_mgf_generating_eq_kernel
    (x ω : ℝ) (u w : ℂ) :
    Complex.exp (-((x : ℂ) ^ 2 / 4)) *
      Complex.exp
        (-(u ^ 2) / 2 - (w ^ 2) / 2 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
          ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
              (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4) =
    Complex.exp
      (u * w +
        (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) * u -
        star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) * w) *
      Complex.ofReal
        (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let z : ℂ := ((x : ℂ) + lam) / (Real.sqrt 2 : ℂ)
  have hz :
      z =
        (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
          (Real.sqrt 2 : ℂ)) := by
    simp [z, lam]
    ring
  have hstar : star z = ((x : ℂ) - lam) / (Real.sqrt 2 : ℂ) := by simp [z, lam]
  have hbig :
      (-(u ^ 2) / 2 - (w ^ 2) / 2 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
          ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4) =
        lam ^ 2 / 4 + (u * w + z * u - star z * w) := by
    rw [hstar]
    simp only [z]
    have hsqrt2_cube : (Real.sqrt 2 : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
      rw [show (Real.sqrt 2 : ℂ) ^ 3 = (Real.sqrt 2 : ℂ) ^ 2 * (Real.sqrt 2 : ℂ)
        by ring]
      rw [sqrtTwoC_sq]
    field_simp [sqrtTwoC_ne]
    ring_nf
    rw [hsqrt2_cube, sqrtTwoC_sq]
    ring
  rw [show
      -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
            (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w =
        lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w by
    simp [lam]]
  rw [hbig, Complex.exp_add, hz]
  calc
    Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        (Complex.exp (lam ^ 2 / 4) *
          Complex.exp
            (u * w +
              (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * u -
                star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                  (Real.sqrt 2 : ℂ)) * w)) =
      Complex.exp
          (u * w +
            (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ)) * u -
              star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                (Real.sqrt 2 : ℂ)) * w) *
        (Complex.exp (-((x : ℂ) ^ 2 / 4)) * Complex.exp (lam ^ 2 / 4)) := by ring
    _ = _ := by
        rw [show lam = -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) by simp [lam]]
        rw [gaussian_half_exp_factor_eq_closed_exp]
private theorem iteratedDeriv_iteratedDeriv_add
    (i j : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv j (iteratedDeriv i f) = iteratedDeriv (j + i) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]
private theorem contDiff_iteratedDeriv_cexp_sq_div_four
    (i n : ℕ) :
    ContDiff ℂ n (iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))) := by
  have hF : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) := by fun_prop
  rw [contDiff_nat_iff_iteratedDeriv]
  constructor
  · intro m hm
    rw [iteratedDeriv_iteratedDeriv_add]
    exact hF.continuous_iteratedDeriv (m + i) (by simp)
  · intro m hm
    rw [iteratedDeriv_iteratedDeriv_add]
    exact hF.differentiable_iteratedDeriv (m + i) (by simp)
private theorem iteratedDeriv_cexp_sq_div_four_affine_at_zero
    (i : ℕ) (lam w : ℂ) :
    iteratedDeriv i
      (fun u : ℂ => Complex.exp
        ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) 0 =
      (Real.sqrt 2 : ℂ) ^ i *
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
          (lam + (Real.sqrt 2 : ℂ) * w) := by
  rw [show
      (fun u : ℂ => Complex.exp
        ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) =
        fun u : ℂ =>
          (fun y : ℂ => Complex.exp ((y + (lam + (Real.sqrt 2 : ℂ) * w)) ^ 2 / 4))
            ((Real.sqrt 2 : ℂ) * u) by
    funext u
    congr 1
    ring]
  have hscale := congrFun
    (iteratedDeriv_comp_const_mul
      (n := i)
      (f := fun y : ℂ => Complex.exp ((y + (lam + (Real.sqrt 2 : ℂ) * w)) ^ 2 / 4))
      (by fun_prop) (Real.sqrt 2 : ℂ)) 0
  rw [hscale]
  rw [show
      (fun y : ℂ => Complex.exp ((y + (lam + (Real.sqrt 2 : ℂ) * w)) ^ 2 / 4)) =
        fun y : ℂ => (fun z : ℂ => Complex.exp (z ^ 2 / 4))
          (y + (lam + (Real.sqrt 2 : ℂ) * w)) by
    rfl]
  have hcomp := congrFun
    (iteratedDeriv_comp_add_const i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
      (lam + (Real.sqrt 2 : ℂ) * w)) 0
  simpa using congrArg (fun y : ℂ => (Real.sqrt 2 : ℂ) ^ i * y) hcomp
private theorem iteratedDeriv_linear_exp_mul_shifted_square_at_zero
    (k : ℕ) (x : ℝ) (lam w : ℂ) :
    iteratedDeriv k
      (fun u : ℂ =>
        Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
          Complex.exp
            ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) 0 =
      (Real.sqrt 2 : ℂ) ^ k *
        (∑ i ∈ Finset.range (k + 1),
          (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w)) := by
  rw [show
      (fun u : ℂ =>
        Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
          Complex.exp
            ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) =
        fun u : ℂ =>
          Complex.exp
            ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4) *
            Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) by
    funext u
    ring]
  rw [iteratedDeriv_fun_mul]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_cexp_sq_div_four_affine_at_zero]
    rw [show
        iteratedDeriv (k - i)
          (fun u : ℂ => Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2)) 0 =
          ((Real.sqrt 2 : ℂ) * (x : ℂ) / 2) ^ (k - i) by
      rw [show
          (fun u : ℂ => Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2)) =
          fun u : ℂ => Complex.exp (((Real.sqrt 2 : ℂ) * (x : ℂ) / 2) * u) by
        funext u
        congr 1
        ring]
      simp [iteratedDeriv_cexp_const_mul]]
    have hi_le : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [show ((Real.sqrt 2 : ℂ) * (x : ℂ) / 2) ^ (k - i) =
        (Real.sqrt 2 : ℂ) ^ (k - i) * ((x : ℂ) / 2) ^ (k - i) by
      rw [show (Real.sqrt 2 : ℂ) * (x : ℂ) / 2 =
          (Real.sqrt 2 : ℂ) * ((x : ℂ) / 2) by ring]
      rw [mul_pow]]
    have hpow : i + (k - i) = k := by omega
    let D : ℂ := iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
      (lam + (Real.sqrt 2 : ℂ) * w)
    let X : ℂ := ((x : ℂ) / 2) ^ (k - i)
    calc
      (Nat.choose k i : ℂ) *
          ((Real.sqrt 2 : ℂ) ^ i * D) *
          ((Real.sqrt 2 : ℂ) ^ (k - i) * X) =
        ((Real.sqrt 2 : ℂ) ^ i * (Real.sqrt 2 : ℂ) ^ (k - i)) *
          ((Nat.choose k i : ℂ) * X * D) := by ring
      _ = (Real.sqrt 2 : ℂ) ^ k * ((Nat.choose k i : ℂ) * X * D) := by rw [← pow_add, hpow]
      _ = (Real.sqrt 2 : ℂ) ^ k *
          ((Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w)) := by simp [D, X]
  · fun_prop
  · fun_prop
private theorem iteratedDeriv_u_shifted_factor_expansion
    (n : ℕ) (x : ℝ) (lam w : ℂ) :
    iteratedDeriv n
      (fun u : ℂ =>
        Complex.exp (-(u ^ 2) / 2) *
          (Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
            Complex.exp
              ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4))) 0 =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0 *
            (∑ i ∈ Finset.range (k + 1),
              (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
                iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                  (lam + (Real.sqrt 2 : ℂ) * w)) := by
  rw [show
      (fun u : ℂ =>
        Complex.exp (-(u ^ 2) / 2) *
          (Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
            Complex.exp
              ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4))) =
        fun u : ℂ =>
          (Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
            Complex.exp
              ((lam + (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2 / 4)) *
            Complex.exp (-(u ^ 2) / 2) by
    funext u
    ring]
  rw [iteratedDeriv_fun_mul]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDeriv_linear_exp_mul_shifted_square_at_zero]
    ring
  · fun_prop
  · fun_prop
private theorem iteratedDeriv_shifted_iterated_cexp_sq_div_four
    (i j : ℕ) (lam : ℂ) :
    iteratedDeriv j
      (fun w : ℂ => iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
        (lam + (Real.sqrt 2 : ℂ) * w)) 0 =
      (Real.sqrt 2 : ℂ) ^ j *
        iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam := by
  rw [show
      (fun w : ℂ => iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
        (lam + (Real.sqrt 2 : ℂ) * w)) =
      fun w : ℂ => (fun y : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam))
          ((Real.sqrt 2 : ℂ) * w) by
    funext w
    congr 1
    ring]
  have hscale := congrFun
    (iteratedDeriv_comp_const_mul
      (n := j)
      (f := fun y : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam))
      (by
        have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i j
        fun_prop)
      (Real.sqrt 2 : ℂ)) 0
  rw [hscale]
  rw [show
      (fun y : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam)) =
      fun y : ℂ => (iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))) (y + lam) by
    rfl]
  have hcomp := congrFun
    (iteratedDeriv_comp_add_const j
      (iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))) lam) 0
  rw [show
      iteratedDeriv j (fun y : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam))
          ((Real.sqrt 2 : ℂ) * 0) =
        iteratedDeriv j (fun y : ℂ =>
          iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4)) (y + lam)) 0 by
    simp]
  rw [hcomp, iteratedDeriv_iteratedDeriv_add]
  simp only [zero_add, mul_eq_mul_left_iff, pow_eq_zero_iff', Complex.ofReal_eq_zero,
    Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]
  rw [Nat.add_comm]
private theorem iteratedDeriv_neg_linear_exp_mul_shifted_iterated_at_zero
    (l i : ℕ) (x : ℝ) (lam : ℂ) :
    iteratedDeriv l
      (fun w : ℂ =>
        Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
          iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (lam + (Real.sqrt 2 : ℂ) * w)) 0 =
      (Real.sqrt 2 : ℂ) ^ l *
        (∑ j ∈ Finset.range (l + 1),
          (Nat.choose l j : ℂ) * (-(x : ℂ) / 2) ^ (l - j) *
            iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam) := by
  rw [show
      (fun w : ℂ =>
        Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
          iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (lam + (Real.sqrt 2 : ℂ) * w)) =
      fun w : ℂ =>
        iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (lam + (Real.sqrt 2 : ℂ) * w) *
          Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) by
    funext w
    ring]
  rw [iteratedDeriv_fun_mul]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedDeriv_shifted_iterated_cexp_sq_div_four]
    rw [show
        iteratedDeriv (l - j)
          (fun w : ℂ => Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2)) 0 =
          (-(Real.sqrt 2 : ℂ) * (x : ℂ) / 2) ^ (l - j) by
      rw [show
          (fun w : ℂ => Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2)) =
          fun w : ℂ => Complex.exp ((-(Real.sqrt 2 : ℂ) * (x : ℂ) / 2) * w) by
        funext w
        congr 1
        ring]
      simp [iteratedDeriv_cexp_const_mul]]
    have hj_le : j ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [show (-(Real.sqrt 2 : ℂ) * (x : ℂ) / 2) ^ (l - j) =
        (Real.sqrt 2 : ℂ) ^ (l - j) * (-(x : ℂ) / 2) ^ (l - j) by
      rw [show -(Real.sqrt 2 : ℂ) * (x : ℂ) / 2 =
          (Real.sqrt 2 : ℂ) * (-(x : ℂ) / 2) by ring]
      rw [mul_pow]]
    have hpow : j + (l - j) = l := by omega
    let D : ℂ := iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam
    let X : ℂ := (-(x : ℂ) / 2) ^ (l - j)
    calc
      (Nat.choose l j : ℂ) *
          ((Real.sqrt 2 : ℂ) ^ j * D) *
          ((Real.sqrt 2 : ℂ) ^ (l - j) * X) =
        ((Real.sqrt 2 : ℂ) ^ j * (Real.sqrt 2 : ℂ) ^ (l - j)) *
          ((Nat.choose l j : ℂ) * X * D) := by ring
      _ = (Real.sqrt 2 : ℂ) ^ l * ((Nat.choose l j : ℂ) * X * D) := by rw [← pow_add, hpow]
      _ = (Real.sqrt 2 : ℂ) ^ l *
          ((Nat.choose l j : ℂ) * (-(x : ℂ) / 2) ^ (l - j) *
            iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam) := by simp [D, X]
  · have hiter : ContDiffAt ℂ l
        (fun w : ℂ => iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
          (lam + (Real.sqrt 2 : ℂ) * w)) 0 := by
      have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i l
      fun_prop
    exact hiter
  · fun_prop
private theorem iteratedDeriv_w_shifted_factor_expansion
    (m i : ℕ) (x : ℝ) (lam : ℂ) :
    iteratedDeriv m
      (fun w : ℂ =>
        Complex.exp (-(w ^ 2) / 2) *
          (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w))) 0 =
      ∑ l ∈ Finset.range (m + 1),
        (Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
          iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0 *
            (∑ j ∈ Finset.range (l + 1),
              (Nat.choose l j : ℂ) * (-(x : ℂ) / 2) ^ (l - j) *
                iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4)) lam) := by
  rw [show
      (fun w : ℂ =>
        Complex.exp (-(w ^ 2) / 2) *
          (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w))) =
      fun w : ℂ =>
        (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
          iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (lam + (Real.sqrt 2 : ℂ) * w)) *
          Complex.exp (-(w ^ 2) / 2) by
    funext w
    ring]
  rw [iteratedDeriv_fun_mul]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [iteratedDeriv_neg_linear_exp_mul_shifted_iterated_at_zero]
    ring
  · have hiter : ContDiffAt ℂ m
        (fun w : ℂ =>
          Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
            iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (lam + (Real.sqrt 2 : ℂ) * w)) 0 := by
      have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i m
      fun_prop
    exact hiter
  · fun_prop
private theorem sum_reorder_left_mul
    (s t : Finset ℕ) (A : ℂ) (B C : ℕ → ℂ) (D : ℕ → ℕ → ℂ) :
    A * (∑ i ∈ s, B i * (∑ l ∈ t, C l * D i l)) =
      ∑ l ∈ t, (A * C l) * (∑ i ∈ s, B i * D i l) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  ring
private theorem left_mul_nested_sum
    (s : Finset ℕ) (t : ℕ → Finset ℕ) (C : ℂ)
    (A : ℕ → ℂ) (B D : ℕ → ℕ → ℂ) :
    C * (∑ k ∈ s, A k * (∑ i ∈ t k, B k i * D k i)) =
      ∑ k ∈ s, A k * (∑ i ∈ t k, B k i * (C * D k i)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show C * (A k * (∑ i ∈ t k, B k i * D k i)) =
      A k * (C * (∑ i ∈ t k, B k i * D k i)) by
    ring]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
private theorem shifted_mgf_mixed_derivative_expansion_unscaled
    (n m : ℕ) (x ω : ℝ) :
    iteratedDeriv m
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp
              (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                    (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0) 0 =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
            iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0) *
          ((Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
            iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0) *
            (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
              (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                  iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                    (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  have hfun :
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp
              (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                    (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0) =
      fun w : ℂ =>
        ∑ k ∈ Finset.range (n + 1),
          ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
            iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0) *
            (∑ i ∈ Finset.range (k + 1),
              (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
                (Complex.exp (-(w ^ 2) / 2) *
                  (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
                    iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (lam + (Real.sqrt 2 : ℂ) * w)))) := by
    funext w
    rw [show
        (fun u : ℂ =>
          Complex.exp
            (-(u ^ 2) / 2 - (w ^ 2) / 2 +
              (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
              (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
              ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                  (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) =
        fun u : ℂ =>
          (Complex.exp (-(w ^ 2) / 2) *
            Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2)) *
            (Complex.exp (-(u ^ 2) / 2) *
              (Complex.exp ((Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2) *
                Complex.exp ((lam + (Real.sqrt 2 : ℂ) * u +
                  (Real.sqrt 2 : ℂ) * w) ^ 2 / 4))) by
      funext u
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp [lam]
      ring]
    rw [iteratedDeriv_const_mul_field,
      iteratedDeriv_u_shifted_factor_expansion,
      left_mul_nested_sum]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_sum]
    · rw [show
          (∑ i ∈ Finset.range (k + 1),
            iteratedDeriv m
              (fun w : ℂ =>
                (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
                  (Complex.exp (-(w ^ 2) / 2) *
                    (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
                      iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                        (lam + (Real.sqrt 2 : ℂ) * w)))) 0) =
          ∑ i ∈ Finset.range (k + 1),
            ((Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i)) *
              (∑ l ∈ Finset.range (m + 1),
                ((Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
                  iteratedDeriv (m - l)
                    (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0) *
                  (∑ j ∈ Finset.range (l + 1),
                    (Nat.choose l j : ℂ) * (-(x : ℂ) / 2) ^ (l - j) *
                      iteratedDeriv (i + j)
                        (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                        (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [iteratedDeriv_const_mul_field, iteratedDeriv_w_shifted_factor_expansion]
        ]
      rw [sum_reorder_left_mul]
      apply Finset.sum_congr rfl
      intro l hl
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · intro i hi
      have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i m
      fun_prop
  · intro k hk
    have hsum : ContDiffAt ℂ m
        (fun w : ℂ =>
          ∑ i ∈ Finset.range (k + 1),
            (Nat.choose k i : ℂ) * ((x : ℂ) / 2) ^ (k - i) *
              (Complex.exp (-(w ^ 2) / 2) *
                (Complex.exp (-(Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2) *
                  iteratedDeriv i (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                    (lam + (Real.sqrt 2 : ℂ) * w)))) 0 := by
      apply ContDiffAt.sum
      intro i hi
      have hFi := contDiff_iteratedDeriv_cexp_sq_div_four i m
      fun_prop
    exact ContDiffAt.const_smul
      ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
        iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0) hsum
private theorem scaled_moment_sum_eq_shifted_mgf_unscaled_sum
    (n m : ℕ) (x ω : ℝ) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹) *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j)
                      (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))))) =
      Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
              iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0) *
            ((Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
              iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) := by
  have hcπ : (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0) := by
    exact_mod_cast (Real.rpow_pos_of_pos Real.pi_pos (-(1 / 2 : ℝ))).ne'
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  unfold realHermiteGeneratingExpansionCoeff
  let A : ℂ :=
    (Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
      iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0
  let B : ℂ :=
    (Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
      iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0
  let S : ℂ :=
    ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
      (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
        ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
          iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
            (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))
  have hscale :
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹ *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) = 1 := by
    have hmul : (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) =
        ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
      by simpa [one_div] using realHermiteGenerating_pi_quarter_mul_self
    simp_all only [one_div, ne_eq, Complex.ofReal_eq_zero, Finset.mem_range, Order.lt_add_one_iff,
      not_false_eq_true, inv_mul_cancel₀]
  calc
    ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹ *
        (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * A *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * B) *
          (Complex.exp (-((x : ℂ) ^ 2 / 4)) * S)) =
      (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹ *
          (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
            ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))) *
        (Complex.exp (-((x : ℂ) ^ 2 / 4)) * (A * B * S)) := by ring
    _ = Complex.exp (-((x : ℂ) ^ 2 / 4)) * (A * B * S) := by
        simp_all only [one_div, ne_eq, Complex.ofReal_eq_zero, Finset.mem_range,
          Order.lt_add_one_iff, one_mul]
    _ = Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          iteratedDeriv (n - k) (fun u : ℂ => Complex.exp (-(u ^ 2) / 2)) 0 *
            ((Nat.choose m l : ℂ) * (Real.sqrt 2 : ℂ) ^ l *
              iteratedDeriv (m - l) (fun w : ℂ => Complex.exp (-(w ^ 2) / 2)) 0) *
          (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
            (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
              ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                  (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) := by simp [A, B, S]
private theorem shifted_mgf_coefficient_eq_kernel_coefficient
    (n m : ℕ) (x ω : ℝ) :
    iteratedDeriv m
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              Complex.exp
                (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                  ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                      (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0) 0 =
      ((-1 : ℂ) ^ m *
        complexHermite n m
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  have hfun :
      (fun w : ℂ =>
        iteratedDeriv n
          (fun u : ℂ =>
            Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              Complex.exp
                (-(u ^ 2) / 2 - (w ^ 2) / 2 +
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
                  (Real.sqrt 2 : ℂ) * (x : ℂ) * w / 2 +
                  ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ) +
                      (Real.sqrt 2 : ℂ) * u + (Real.sqrt 2 : ℂ) * w) ^ 2) / 4)) 0) =
        fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ => Complex.exp (u * w + z * u - star z * w) * E) 0 := by
    funext w
    congr 1
    funext u
    exact shifted_mgf_generating_eq_kernel x ω u w
  rw [hfun]
  have hinner :
      (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ => Complex.exp (u * w + z * u - star z * w) * E) 0) =
        fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0 * E := by
    simp_all only [neg_mul, iteratedDeriv_const_mul_field, RCLike.star_def,
      iteratedDeriv_mul_const_field]
  rw [hinner, iteratedDeriv_mul_const_field, iteratedDeriv_cexp_ambiguity_kernel_at_zero]
private theorem oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial
    (k l : ℕ) (x ω t : ℝ) :
    oneDWindowAmbiguityMonomialKernel k l x ω t =
      (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l) *
        oneDWindowAmbiguityShiftedModulatedGaussian x ω t := by
  rw [oneDWindowAmbiguityMonomialKernel, star_complex_monomial_gaussian]
  unfold complexMonomialGaussian oneDWindowAmbiguityShiftedModulatedGaussian
  have hexp :
      Complex.exp (-((((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) *
          Complex.exp (-((((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) =
        Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num
    ring
  have hinner : ((inner ℝ ω t : ℝ) : ℂ) = (ω : ℂ) * (t : ℂ) := by
    simp [inner]
    ring
  rw [hinner]
  rw [show
      (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          Complex.exp (-((((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2))) *
        (((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
          Complex.exp (-((((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2))) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
      (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l) *
        (Complex.exp (-((((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2)) *
          Complex.exp (-((((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ 2) / 2))) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) by
    ring]
  rw [hexp]
  ring
private theorem oneDWindowAmbiguityMonomialKernel_normalized_integral_eq_gaussian_moment
    (k l : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel k l x ω t) =
      Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        ∫ t : ℝ,
          (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
            ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
            ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) := by
  let f : ℝ → ℂ := fun t =>
    (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
      ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
  rw [integral_gaussian_zero_half_eq_density f, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial]
  unfold oneDWindowAmbiguityShiftedModulatedGaussian f
  rw [show Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) =
      Complex.exp (-((t : ℂ) ^ 2)) * Complex.exp (-((x : ℂ) ^ 2 / 4)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring
private theorem shifted_monomial_pair_expansion
    (k l : ℕ) (t a b E : ℂ) :
    (t + a) ^ k * (t + b) ^ l * E =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
        (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          a ^ (k - i) * b ^ (l - j) * (t ^ (i + j) * E) := by
  rw [add_pow, add_pow]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring
private theorem shifted_monomial_pair_modulated_expansion
    (k l : ℕ) (x ω t : ℝ) :
    (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
        (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
            ((t : ℂ) ^ (i + j) *
              Complex.exp ((-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) * (t : ℂ))) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let a : ℂ := (x : ℂ) / 2
  let b : ℂ := -(x : ℂ) / 2
  have hplus :
      ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) = (t : ℂ) + a := by
    simp [a]
    ring
  have hminus :
      ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) = (t : ℂ) + b := by
    simp [b]
    ring
  have hphase :
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
        Complex.exp (lam * (t : ℂ)) := by
    congr 1
    simp [lam]
    ring
  rw [hplus, hminus, hphase]
  exact shifted_monomial_pair_expansion k l (t : ℂ) a b
    (Complex.exp (lam * (t : ℂ)))
private theorem gaussian_half_shifted_monomial_pair_exp_integrable
    (k l : ℕ) (x ω : ℝ) :
    Integrable
      (fun t : ℝ =>
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
      )
      (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let a : ℂ := (x : ℂ) / 2
  let b : ℂ := -(x : ℂ) / 2
  have hpoint :
      (fun t : ℝ =>
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))) =
      fun t : ℝ =>
        ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
          (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
            a ^ (k - i) * b ^ (l - j) *
              ((t : ℂ) ^ (i + j) * Complex.exp (lam * (t : ℂ))) := by
    funext t
    exact shifted_monomial_pair_modulated_expansion k l x ω t
  rw [hpoint]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (gaussian_half_integrable_monomial_exp (i + j) lam).const_mul
    ((Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
      a ^ (k - i) * b ^ (l - j))
private theorem oneDWindowAmbiguityMonomialKernel_normalized_integrable
    (k l : ℕ) (x ω : ℝ) :
    Integrable
      (fun t : ℝ =>
        ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          oneDWindowAmbiguityMonomialKernel k l x ω t)
      (volume : Measure ℝ) := by
  let g : ℝ → ℂ := fun t =>
    (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
      ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
  let ex : ℂ := Complex.exp (-((x : ℂ) ^ 2 / 4))
  have hg_gauss :
      Integrable g (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) := by
    exact gaussian_half_shifted_monomial_pair_exp_integrable k l x ω
  have hgauss_eq :
      ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal) =
        (volume : Measure ℝ).withDensity (ProbabilityTheory.gaussianPDF 0 (1 / 2 : NNReal)) :=
    ProbabilityTheory.gaussianReal_of_var_ne_zero 0
      (by norm_num : (1 / 2 : NNReal) ≠ 0)
  have hg_density :
      Integrable g
        ((volume : Measure ℝ).withDensity
          (ProbabilityTheory.gaussianPDF 0 (1 / 2 : NNReal))) := by
    simp_all only [one_div]
  have hpdf_meas :
      Measurable (ProbabilityTheory.gaussianPDF 0 (1 / 2 : NNReal)) :=
    ProbabilityTheory.measurable_gaussianPDF 0 (1 / 2 : NNReal)
  have hpdf_ne_top :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ProbabilityTheory.gaussianPDF 0 (1 / 2 : NNReal) t < ∞ :=
    ae_of_all _ fun t => ProbabilityTheory.gaussianPDF_lt_top
  have hg_volume :=
    (integrable_withDensity_iff_integrable_smul' hpdf_meas hpdf_ne_top).1 hg_density
  refine (hg_volume.const_mul ex).congr ?_
  filter_upwards with t
  rw [oneDWindowAmbiguityMonomialKernel_eq_shifted_monomial]
  unfold oneDWindowAmbiguityShiftedModulatedGaussian g ex
  rw [show Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) =
      Complex.exp (-((t : ℂ) ^ 2)) * Complex.exp (-((x : ℂ) ^ 2 / 4)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  rw [ProbabilityTheory.toReal_gaussianPDF]
  change Complex.exp (-((x : ℂ) ^ 2 / 4)) *
      (((ProbabilityTheory.gaussianPDFReal 0 (1 / 2 : NNReal) t : ℝ) : ℂ) *
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))) =
    ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
          (Complex.exp (-((t : ℂ) ^ 2)) *
            Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))))
  rw [gaussianPDFReal_zero_half_eq]
  ring_nf
private theorem gaussian_half_shifted_monomial_pair_exp_integral
    (k l : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))
        ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
        (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
            iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
              (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) := by
  let lam : ℂ := -(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)
  let a : ℂ := (x : ℂ) / 2
  let b : ℂ := -(x : ℂ) / 2
  have hpoint :
      (fun t : ℝ =>
        (((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ k *
          ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) ^ l *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))))) =
      fun t : ℝ =>
        ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
          (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
            a ^ (k - i) * b ^ (l - j) *
              ((t : ℂ) ^ (i + j) * Complex.exp (lam * (t : ℂ))) := by
    funext t
    have hplus :
        ((t + (1 / 2 : ℝ) * x : ℝ) : ℂ) = (t : ℂ) + a := by
      simp [a]
      ring
    have hminus :
        ((t - (1 / 2 : ℝ) * x : ℝ) : ℂ) = (t : ℂ) + b := by
      simp [b]
      ring
    have hphase :
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ))) =
          Complex.exp (lam * (t : ℂ)) := by
      congr 1
      simp [lam]
      ring
    rw [hplus, hminus, hphase]
    exact shifted_monomial_pair_expansion k l (t : ℂ) a b
      (Complex.exp (lam * (t : ℂ)))
  rw [hpoint, MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      let c : ℂ :=
        (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          a ^ (k - i) * b ^ (l - j)
      rw [show
          (∫ t : ℝ,
            (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
              a ^ (k - i) * b ^ (l - j) *
                ((t : ℂ) ^ (i + j) * Complex.exp (lam * (t : ℂ)))
              ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))) =
            c * ∫ t : ℝ,
              ((t : ℂ) ^ (i + j) * Complex.exp (lam * (t : ℂ)))
              ∂(ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)) by
        simp only [c]
        exact MeasureTheory.integral_const_mul ..]
      rw [gaussian_half_moment_eq_iteratedDeriv]
    · intro j hj
      exact (gaussian_half_integrable_monomial_exp (i + j) lam).const_mul
        ((Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
          a ^ (k - i) * b ^ (l - j))
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (gaussian_half_integrable_monomial_exp (i + j) lam).const_mul
      ((Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
        a ^ (k - i) * b ^ (l - j))
private theorem oneDWindowAmbiguityMonomialKernel_normalized_integral_eq_moment_sum
    (k l : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        oneDWindowAmbiguityMonomialKernel k l x ω t) =
      Complex.exp (-((x : ℂ) ^ 2 / 4)) *
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
          (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
            ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
              iteratedDeriv (i + j) (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))) := by
  rw [oneDWindowAmbiguityMonomialKernel_normalized_integral_eq_gaussian_moment,
    gaussian_half_shifted_monomial_pair_exp_integral]
private theorem real_pi_neg_half_complex_ne_zero :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0) := by
  exact_mod_cast (Real.rpow_pos_of_pos Real.pi_pos (-(1 / 2 : ℝ))).ne'
private theorem iteratedDeriv_generating_cross_ambiguity_kernel_integral_coefficient
    (n m : ℕ) (x ω : ℝ) :
    iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                  realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 =
      ((-1 : ℂ) ^ m *
        complexHermite n m
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  rw [ambiguity_kernel_iteratedDeriv_factor n x ω, iteratedDeriv_mul_const_field,
    iteratedDeriv_cexp_ambiguity_kernel_at_zero]
private theorem iteratedDeriv_generating_cross_ambiguity_integrand_finite_expansion
    (n m : ℕ) (x ω t : ℝ) :
    iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
        iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ)) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          oneDWindowAmbiguityMonomialKernel k l x ω t := by
  rw [realHermiteGenerating_iteratedDeriv_zero_expansion_monomial,
    realHermiteGenerating_iteratedDeriv_zero_expansion_monomial]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  simp [oneDWindowAmbiguityMonomialKernel, star_complex_monomial_gaussian]
  ring
private theorem iteratedDeriv_generating_cross_ambiguity_normalized_integral_finite_sum
    (n m : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (∫ t : ℝ,
            ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              oneDWindowAmbiguityMonomialKernel k l x ω t) := by
  let cπ : ℂ := ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  calc
    (∫ t : ℝ,
      cπ *
        (iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))) =
        ∫ t : ℝ,
          ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
            (realHermiteGeneratingExpansionCoeff n k *
                realHermiteGeneratingExpansionCoeff m l) *
              (cπ * oneDWindowAmbiguityMonomialKernel k l x ω t) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [iteratedDeriv_generating_cross_ambiguity_integrand_finite_expansion, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          ring
    _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        ∫ t : ℝ,
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (cπ * oneDWindowAmbiguityMonomialKernel k l x ω t) := by
          rw [MeasureTheory.integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro k hk
            rw [MeasureTheory.integral_finsetSum]
            intro l hl
            exact (oneDWindowAmbiguityMonomialKernel_normalized_integrable k l x ω).const_mul
              (realHermiteGeneratingExpansionCoeff n k *
                realHermiteGeneratingExpansionCoeff m l)
          · intro k hk
            apply integrable_finsetSum
            intro l hl
            exact (oneDWindowAmbiguityMonomialKernel_normalized_integrable k l x ω).const_mul
              (realHermiteGeneratingExpansionCoeff n k *
                realHermiteGeneratingExpansionCoeff m l)
    _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (∫ t : ℝ, cπ * oneDWindowAmbiguityMonomialKernel k l x ω t) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          exact MeasureTheory.integral_const_mul ..
private theorem iteratedDeriv_generating_cross_ambiguity_normalized_integral_moment_sum
    (n m : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ)))) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
            (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
              (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                  iteratedDeriv (i + j)
                    (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                    (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) := by
  rw [iteratedDeriv_generating_cross_ambiguity_normalized_integral_finite_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [oneDWindowAmbiguityMonomialKernel_normalized_integral_eq_moment_sum]
private theorem iteratedDeriv_generating_cross_ambiguity_pi_neg_half_mul_integral_moment_sum
    (n m : ℕ) (x ω : ℝ) :
    ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (∫ t : ℝ,
        iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (realHermiteGeneratingExpansionCoeff n k *
            realHermiteGeneratingExpansionCoeff m l) *
          (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
            (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
              (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                  iteratedDeriv (i + j)
                    (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                    (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)))) := by
  rw [← MeasureTheory.integral_const_mul]
  exact iteratedDeriv_generating_cross_ambiguity_normalized_integral_moment_sum n m x ω
private theorem iteratedDeriv_generating_cross_ambiguity_integral_moment_sum
    (n m : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
        iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹) *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j)
                      (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))))) := by
  let cπ : ℂ := ((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  have hcπ : cπ ≠ 0 := by exact real_pi_neg_half_complex_ne_zero
  have h :=
    iteratedDeriv_generating_cross_ambiguity_pi_neg_half_mul_integral_moment_sum n m x ω
  calc
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
        iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
        cπ⁻¹ * (cπ *
          (∫ t : ℝ,
            iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
              iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
                Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                  ((inner ℝ ω t : ℝ) : ℂ)))) := by rw [← mul_assoc, inv_mul_cancel₀ hcπ, one_mul]
    _ = cπ⁻¹ *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j)
                      (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))))) := by rw [h]
private theorem iteratedDeriv_generating_cross_ambiguity_moment_sum_eq_kernel_coefficient
    (n m : ℕ) (x ω : ℝ) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)⁻¹) *
        (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
          (realHermiteGeneratingExpansionCoeff n k *
              realHermiteGeneratingExpansionCoeff m l) *
            (Complex.exp (-((x : ℂ) ^ 2 / 4)) *
              (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (l + 1),
                (Nat.choose k i : ℂ) * (Nat.choose l j : ℂ) *
                  ((x : ℂ) / 2) ^ (k - i) * (-(x : ℂ) / 2) ^ (l - j) *
                    iteratedDeriv (i + j)
                      (fun z : ℂ => Complex.exp (z ^ 2 / 4))
                      (-(2 * Real.pi : ℂ) * Complex.I * (ω : ℂ))))) =
      ((-1 : ℂ) ^ m *
        complexHermite n m
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ))) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  /-
  Pure finite coefficient identity.  After expanding the two real-Hermite
  generating coefficients and evaluating shifted Gaussian half-moments, this is
  exactly the coefficient of `u^n w^m` in the closed kernel
  `Complex.exp (u * w + z * u - star z * w)` times the scalar Gaussian factor.
  -/
  rw [← shifted_mgf_coefficient_eq_kernel_coefficient n m x ω,
    scaled_moment_sum_eq_shifted_mgf_unscaled_sum,
    ← shifted_mgf_mixed_derivative_expansion_unscaled]
  simp only [neg_mul, iteratedDeriv_const_mul_field]
private theorem iteratedDeriv_generating_cross_ambiguity_integral_eq_kernel_coefficient
    (n m : ℕ) (x ω : ℝ) :
    (∫ t : ℝ,
      iteratedDeriv n (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
        iteratedDeriv m (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ω t : ℝ) : ℂ))) =
      iteratedDeriv m
        (fun w : ℂ =>
          iteratedDeriv n
            (fun u : ℂ =>
              ∫ t : ℝ,
                realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                  realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                      ((inner ℝ ω t : ℝ) : ℂ))) 0) 0 := by
  rw [iteratedDeriv_generating_cross_ambiguity_integral_moment_sum,
    iteratedDeriv_generating_cross_ambiguity_kernel_integral_coefficient]
  exact iteratedDeriv_generating_cross_ambiguity_moment_sum_eq_kernel_coefficient n m x ω
private theorem realHermiteTensor_stft_integral_formula_of_oneD
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d)
    (h1D : ∀ q : Fin d,
      (∫ s : ℝ,
        realHermite1D (alpha q) s *
          star (realHermite1D (kappa q) (s - ξ.1 q)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ (ξ.2 q) s : ℝ) : ℂ))) =
        (-1 : ℂ) ^ kappa q *
          Complex.exp (-(Real.pi : ℂ) * Complex.I *
            (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) *
            (Complex.ofReal
              (Real.exp (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))) *
              phi1D (kappa q) (alpha q) (TKappa ξ q))) :
    (∫ t : RealVec d,
      realHermiteTensorRep alpha t *
        star (realHermiteTensorRep kappa (t - ξ.1)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) *
          Phi kappa alpha (TKappa ξ)) := by
  rw [tensorRep_stft_integral_eq_prod_oneD]
  rw [show
      (∏ q : Fin d,
        ∫ s : ℝ,
          realHermite1D (alpha q) s *
            star (realHermite1D (kappa q) (s - ξ.1 q)) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ (ξ.2 q) s : ℝ) : ℂ))) =
        ∏ q : Fin d,
          (-1 : ℂ) ^ kappa q *
            Complex.exp (-(Real.pi : ℂ) * Complex.I *
              (((ξ.1 q : ℝ) : ℂ) * (ξ.2 q : ℂ))) *
              (Complex.ofReal
                (Real.exp (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))) *
                phi1D (kappa q) (alpha q) (TKappa ξ q)) by
    simp_all only [RCLike.star_def, neg_mul, RCLike.inner_apply, conj_trivial, Complex.ofReal_mul,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_pow, Complex.ofReal_ofNat]]
  exact prod_oneDRealHermiteSTFT_closed_eq_model kappa alpha ξ
private theorem realHermiteTensor_stft_integral_formula
    {d : Nat} (hd : 0 < d) (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    (∫ t : RealVec d,
      realHermiteTensorRep alpha t *
        star (realHermiteTensorRep kappa (t - ξ.1)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) *
          Phi kappa alpha (TKappa ξ)) := by
  let _ := hd
  exact realHermiteTensor_stft_integral_formula_of_oneD kappa alpha ξ
    (fun q =>
      realHermite1D_stft_integral_formula_of_halfCentered_interchange
        (alpha q) (kappa q) (ξ.1 q) (ξ.2 q)
        (iteratedDeriv_generating_cross_ambiguity_integral_eq_kernel_coefficient
          (alpha q) (kappa q) (ξ.1 q) (ξ.2 q)))
private theorem stft_model_basis_formula
    {d : Nat} (hd : 0 < d) (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    stftRep (varphiKappa kappa) (realHermiteTensorL2 alpha) ξ =
      stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) *
          Phi kappa alpha (TKappa ξ)) := by
  rw [stftRep_varphiKappa_realHermiteTensorL2_eq_tensorRep_integral]
  exact realHermiteTensor_stft_integral_formula hd kappa alpha ξ
private theorem stft_model_global_phase_of_basis_formula
    {d : Nat} (kappa : MultiIndex d)
    (hbasis : ∀ (alpha : Idx d) (ξ : PhaseSpace d),
      stftRep (varphiKappa kappa) (realHermiteTensorL2 alpha) ξ =
        stftModelPhase kappa ξ *
          (((WKappa ξ : ℝ) : ℂ) *
            Phi kappa alpha (TKappa ξ))) :
    ∃ theta : PhaseSpace d -> ℂ,
      (∀ ξ : PhaseSpace d, ‖theta ξ‖ = 1) ∧
        ∀ (U : Skappa d kappa) (ξ : PhaseSpace d),
          stftRep (varphiKappa kappa) (bKappa kappa U) ξ =
            theta ξ * (((WKappa ξ : ℝ) : ℂ) *
              toFun kappa U (TKappa ξ)) := by
  refine ⟨stftModelPhase kappa, stftModelPhase_norm kappa, ?_⟩
  intro U ξ
  let y : L2Real d := modulateL2 ξ.2 (star (translateL2 (-ξ.1) (varphiKappa kappa)))
  let L : L2Real d →L[ℂ] ℂ :=
    ((ContinuousLinearMap.apply ℂ ℂ) y).comp
      (((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2) : L2Real d →L[ℂ] L2Real d →L[ℂ] ℂ)
  have hsummable :
      Summable (fun alpha : Idx d =>
        coeffSkappa U alpha • realHermiteTensorL2 alpha) :=
    summable_realHermiteTensorL2_coeff_smul_of_orthonormal kappa
      (realHermiteTensorL2_orthonormal (d := d)) U
  have hmap :
      L (bKappa kappa U) =
        ∑' alpha : Idx d, L (coeffSkappa U alpha • realHermiteTensorL2 alpha) := by
    unfold bKappa
    exact ContinuousLinearMap.map_tsum L hsummable
  have hstft :
      ∀ f : L2Real d, stftRep (varphiKappa kappa) f ξ = L f := by
    intro f
    exact stftRep_eq_lpPairing (varphiKappa kappa) f ξ
  calc
    stftRep (varphiKappa kappa) (bKappa kappa U) ξ =
        L (bKappa kappa U) := hstft (bKappa kappa U)
    _ = ∑' alpha : Idx d, L (coeffSkappa U alpha • realHermiteTensorL2 alpha) := hmap
    _ = ∑' alpha : Idx d,
        coeffSkappa U alpha *
          stftRep (varphiKappa kappa) (realHermiteTensorL2 alpha) ξ := by
          apply tsum_congr
          intro alpha
          rw [map_smul]
          simp [hstft]
    _ = ∑' alpha : Idx d,
        coeffSkappa U alpha *
          (stftModelPhase kappa ξ *
            (((WKappa ξ : ℝ) : ℂ) *
              Phi kappa alpha (TKappa ξ))) := by
          simp_all only [Prod.forall, map_smul, smul_eq_mul, Subtype.forall, Prod.mk.eta]
    _ = ∑' alpha : Idx d,
        (stftModelPhase kappa ξ * ((WKappa ξ : ℝ) : ℂ)) *
          (coeffSkappa U alpha * Phi kappa alpha (TKappa ξ)) := by
          apply tsum_congr
          intro alpha
          ring
    _ = (stftModelPhase kappa ξ * ((WKappa ξ : ℝ) : ℂ)) *
        ∑' alpha : Idx d, coeffSkappa U alpha * Phi kappa alpha (TKappa ξ) := by rw [tsum_mul_left]
    _ = stftModelPhase kappa ξ *
        (((WKappa ξ : ℝ) : ℂ) * toFun kappa U (TKappa ξ)) := by
          simp [toFun]
          ring
private theorem stft_model_global_phase
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    ∃ theta : PhaseSpace d -> ℂ,
      (∀ ξ : PhaseSpace d, ‖theta ξ‖ = 1) ∧
        ∀ (U : Skappa d kappa) (ξ : PhaseSpace d),
          stftRep (varphiKappa kappa) (bKappa kappa U) ξ =
            theta ξ * (((WKappa ξ : ℝ) : ℂ) *
              toFun kappa U (TKappa ξ)) := stft_model_global_phase_of_basis_formula kappa
    (fun alpha ξ => stft_model_basis_formula hd kappa alpha ξ)
private theorem stft_model_modulus_of_global_phase_formula
    {d : Nat} (kappa : MultiIndex d) (theta : PhaseSpace d -> ℂ)
    (htheta : ∀ ξ : PhaseSpace d, ‖theta ξ‖ = 1)
    (hmodel : ∀ (U : Skappa d kappa) (ξ : PhaseSpace d),
      stftRep (varphiKappa kappa) (bKappa kappa U) ξ =
        theta ξ * (((WKappa ξ : ℝ) : ℂ) *
          toFun kappa U (TKappa ξ)))
    (U : Skappa d kappa) (ξ : PhaseSpace d) :
    ‖stftRep (varphiKappa kappa) (bKappa kappa U) ξ‖ =
      WKappa ξ * ‖toFun kappa U (TKappa ξ)‖ := by
  rw [hmodel U ξ]
  have hW_nonneg : 0 ≤ WKappa ξ := le_of_lt (WKappa_pos ξ)
  simp_all only [Prod.forall, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul,
    mul_eq_mul_right_iff, abs_eq_self, norm_eq_zero, true_or]
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (U : Skappa d kappa) (ξ : PhaseSpace d) :
    ‖stftRep (varphiKappa kappa) (bKappa kappa U) ξ‖ =
      WKappa ξ * ‖toFun kappa U (TKappa ξ)‖ := by
  let _ := hd
  have hphase_model :=
    stft_model_global_phase hd kappa
  rcases hphase_model with ⟨theta, htheta, hmodel⟩
  exact stft_model_modulus_of_global_phase_formula kappa theta htheta hmodel U ξ
end DimdPolyLEAN
