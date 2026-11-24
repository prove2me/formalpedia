-- Prove2me | solution 1 for DimdPolyLEAN.windowAmbiguity_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:22.015162+00:00
-- url     : https://prove2.me/submissions/58e76160-83a7-421c-a752-15fad0cad494

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_ambiguity_integral_independent_kernel
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_expansion_monomial
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_star
public import Theorems.Thm_DimdPolyLEAN_varphiKappa_coe_ae_eq_realHermiteTensorRep
public import Theorems.Thm_DimdPolyLEAN_ambiguityRep_eq_integral_of_ae_eq
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
private theorem iteratedDeriv_cexp_ambiguity_kernel_diag_at_zero
    (k : ℕ) (z : ℂ) :
    iteratedDeriv k
      (fun w : ℂ =>
        iteratedDeriv k
          (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 =
      (-1 : ℂ) ^ k * complexHermite k k z := by
  exact iteratedDeriv_cexp_ambiguity_kernel_at_zero k k z
private theorem inv_factorial_mul_complexHermite_self_eq_phi1D
    (k : ℕ) (z : ℂ) :
    ((Nat.factorial k : ℂ)⁻¹) * complexHermite k k z = phi1D k k z := by
  have hsqrt :
      Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial k : ℝ)) =
        (Nat.factorial k : ℝ) := by
    simp_all only [Nat.cast_nonneg, Real.sqrt_mul_self]
  rw [phi1D, hsqrt]
  norm_num
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
private theorem ambiguityRep_varphiKappa_eq_tensorRep_integral
    {d : Nat} (kappa : MultiIndex d) (ξ : PhaseSpace d) :
    ambiguityRep (varphiKappa kappa) (varphiKappa kappa) ξ =
      ∫ t : RealVec d,
        realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
          star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ)) := by
  have hcoe := varphiKappa_coe_ae_eq_realHermiteTensorRep kappa
  exact ambiguityRep_eq_integral_of_ae_eq hcoe hcoe ξ
private theorem oneDWindowAmbiguityFactor_eq_scaled_iteratedDeriv_integral
    (k : Nat) (x ω : ℝ) :
    oneDWindowAmbiguityFactor k x ω =
      ((Nat.factorial k : ℂ)⁻¹) *
        ∫ t : ℝ,
          iteratedDeriv k (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
            iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ ω t : ℝ) : ℂ)) := by
  let c : ℂ := (Real.sqrt (Nat.factorial k : ℝ) : ℂ) / (Nat.factorial k : ℂ)
  have hc_star : star c = c := by simp [c]
  have hfac_ne : (Nat.factorial k : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hsqrt_sq :
      ((Real.sqrt (Nat.factorial k : ℝ) : ℂ) ^ (2 : ℕ)) =
        (Nat.factorial k : ℂ) := by
    rw [← Complex.ofReal_pow]
    simp_all only [RCLike.star_def, ne_eq, Nat.cast_eq_zero, Nat.cast_nonneg, Real.sq_sqrt,
      Complex.ofReal_natCast]
  have hc_sq : c * c = (Nat.factorial k : ℂ)⁻¹ := by
    dsimp [c]
    field_simp [hfac_ne]
    rw [hsqrt_sq]
  unfold oneDWindowAmbiguityFactor realHermite1D
  change (∫ t : ℝ,
      (c * iteratedDeriv k (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0) *
        star (c * iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))) =
    ((Nat.factorial k : ℂ)⁻¹) *
      ∫ t : ℝ,
        iteratedDeriv k (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))
  rw [← hc_sq, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [star_mul, hc_star, realHermiteGenerating_iteratedDeriv_zero_star]
  ring
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
private theorem oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient_of_interchange
    (k : Nat) (x ω : ℝ)
    (hinterchange :
      (∫ t : ℝ,
        iteratedDeriv k (realHermiteGenerating (t + (1 / 2 : ℝ) * x)) 0 *
          iteratedDeriv k (realHermiteGenerating (t - (1 / 2 : ℝ) * x)) 0 *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ω t : ℝ) : ℂ))) =
        iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv k
              (fun u : ℂ =>
                ∫ t : ℝ,
                  realHermiteGenerating (t + (1 / 2 : ℝ) * x) u *
                    realHermiteGenerating (t - (1 / 2 : ℝ) * x) w *
                      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                        ((inner ℝ ω t : ℝ) : ℂ))) 0) 0) :
    oneDWindowAmbiguityFactor k x ω =
      ((Nat.factorial k : ℂ)⁻¹) *
        (iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv k
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) := by
  rw [oneDWindowAmbiguityFactor_eq_scaled_iteratedDeriv_integral, hinterchange]
  rw [ambiguity_kernel_iteratedDeriv_factor k x ω, iteratedDeriv_mul_const_field]
private theorem oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient
    (k : Nat) (x ω : ℝ) :
    oneDWindowAmbiguityFactor k x ω =
      ((Nat.factorial k : ℂ)⁻¹) *
        (iteratedDeriv k
          (fun w : ℂ =>
            iteratedDeriv k
              (fun u : ℂ =>
                Complex.exp
                  (u * w +
                    (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * u -
                      star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                        (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
          Complex.ofReal
            (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))) := by
  apply oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient_of_interchange
  exact iteratedDeriv_generating_cross_ambiguity_integral_eq_kernel_coefficient k k x ω
private theorem oneDWindowAmbiguityFactor_eq_of_normalized_kernel_coefficient
    (k : Nat) (x ω : ℝ)
    (hcoeff :
      oneDWindowAmbiguityFactor k x ω =
        ((Nat.factorial k : ℂ)⁻¹) *
          (iteratedDeriv k
            (fun w : ℂ =>
              iteratedDeriv k
                (fun u : ℂ =>
                  Complex.exp
                    (u * w +
                      (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                          (Real.sqrt 2 : ℂ)) * u -
                        star (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
                          (Real.sqrt 2 : ℂ)) * w)) 0) 0 *
            Complex.ofReal
              (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))))) :
    oneDWindowAmbiguityFactor k x ω =
      (-1 : ℂ) ^ k *
        phi1D k k
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) := by
  let z : ℂ :=
    ((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
      (Real.sqrt 2 : ℂ)
  let E : ℂ :=
    Complex.ofReal
      (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4)))
  change oneDWindowAmbiguityFactor k x ω =
    (-1 : ℂ) ^ k * phi1D k k z * E
  rw [hcoeff]
  change ((Nat.factorial k : ℂ)⁻¹) *
      (iteratedDeriv k
        (fun w : ℂ =>
          iteratedDeriv k
            (fun u : ℂ => Complex.exp (u * w + z * u - star z * w)) 0) 0 * E) =
    (-1 : ℂ) ^ k * phi1D k k z * E
  rw [iteratedDeriv_cexp_ambiguity_kernel_diag_at_zero,
    ← inv_factorial_mul_complexHermite_self_eq_phi1D k z]
  ring
private theorem oneDWindowAmbiguityFactor_closed
    (k : Nat) (x ω : ℝ) :
    oneDWindowAmbiguityFactor k x ω =
      (-1 : ℂ) ^ k *
        phi1D k k
          (((x : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) /
            (Real.sqrt 2 : ℂ)) *
        Complex.ofReal
          (Real.exp (-((x ^ 2 + (2 * Real.pi) ^ 2 * ω ^ 2) / 4))) :=
  oneDWindowAmbiguityFactor_eq_of_normalized_kernel_coefficient k x ω
    (oneDWindowAmbiguityFactor_eq_normalized_kernel_coefficient k x ω)
private theorem tensorRep_windowAmbiguity_integral_eq_prod_oneD
    {d : Nat} (kappa : MultiIndex d) (ξ : PhaseSpace d) :
    (∫ t : RealVec d,
      realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
        star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      ∏ q : Fin d, oneDWindowAmbiguityFactor (kappa q) (ξ.1 q) (ξ.2 q) := by
  classical
  let f : (q : Fin d) → ℝ → ℂ := fun q t =>
    realHermite1D (kappa q) (t + (1 / 2 : ℝ) * ξ.1 q) *
      star (realHermite1D (kappa q) (t - (1 / 2 : ℝ) * ξ.1 q)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ (ξ.2 q) t : ℝ) : ℂ))
  have h_real_to_pi :
      (∫ t : RealVec d,
        realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
          star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
        ∫ y : Fin d → ℝ, ∏ q : Fin d, f q (y q) := by
    calc
      (∫ t : RealVec d,
        realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
          star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
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
            simp_all only [neg_mul, RCLike.inner_apply, conj_trivial, Complex.ofReal_mul, one_div,
              PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply, RCLike.star_def]
      _ = ∫ y : Fin d → ℝ, ∏ q : Fin d, f q (y q) := by
            simpa [MeasurableEquiv.coe_toLp_symm] using
              (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
                (g := fun y : Fin d → ℝ => ∏ q : Fin d, f q (y q))
  rw [h_real_to_pi]
  exact
    MeasureTheory.integral_fintype_prod_volume_eq_prod
      (f := fun q (t : ℝ) => f q t)
private theorem prod_oneDWindowAmbiguity_closed_eq_PKappa_exp
    {d : Nat} (kappa : MultiIndex d) (ξ : PhaseSpace d) :
    (∏ q : Fin d,
      ((-1 : ℂ) ^ kappa q * phi1D (kappa q) (kappa q) (TKappa ξ q) *
        Complex.ofReal
          (Real.exp
            (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))))) =
      PKappa kappa ξ * Complex.ofReal (Real.exp (-(QKappa ξ))) := by
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
  have hprod_exp :
      (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) =
        Complex.ofReal (Real.exp (-(QKappa ξ))) := by
    calc
      (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) =
          ∏ q : Fin d, Complex.exp (((-(coordQ q) : ℝ) : ℂ)) := by
            simp_all only [Complex.ofReal_exp, Complex.ofReal_neg]
      _ = Complex.exp (∑ q : Fin d, (((-(coordQ q) : ℝ) : ℂ))) := by rw [Complex.exp_sum]
      _ = Complex.ofReal (Real.exp (-(QKappa ξ))) := by
            simp_all only [Complex.ofReal_neg, Finset.sum_neg_distrib, Complex.ofReal_exp,
              Complex.ofReal_sum]
  calc
    (∏ q : Fin d,
      ((-1 : ℂ) ^ kappa q * phi1D (kappa q) (kappa q) (TKappa ξ q) *
        Complex.ofReal
          (Real.exp
            (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4))))) =
        (∏ q : Fin d, (-1 : ℂ) ^ kappa q) *
          (∏ q : Fin d, phi1D (kappa q) (kappa q) (TKappa ξ q)) *
            (∏ q : Fin d, Complex.ofReal (Real.exp (-(coordQ q)))) := by
          simp [coordQ, Finset.prod_mul_distrib, mul_assoc]
    _ = PKappa kappa ξ * Complex.ofReal (Real.exp (-(QKappa ξ))) := by
          rw [hprod_pow, hprod_exp]
          simp [PKappa, Phi, mul_assoc]
private theorem tensorRep_windowAmbiguity_integral_eq_PKappa_exp_of_oneD
    {d : Nat} (kappa : MultiIndex d) (ξ : PhaseSpace d)
    (h1D : ∀ q : Fin d,
      oneDWindowAmbiguityFactor (kappa q) (ξ.1 q) (ξ.2 q) =
        (-1 : ℂ) ^ kappa q * phi1D (kappa q) (kappa q) (TKappa ξ q) *
          Complex.ofReal
            (Real.exp
              (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4)))) :
    (∫ t : RealVec d,
      realHermiteTensorRep kappa (t + ((1 / 2 : ℝ) • ξ.1)) *
        star (realHermiteTensorRep kappa (t - ((1 / 2 : ℝ) • ξ.1))) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ ξ.2 t : ℝ) : ℂ))) =
      PKappa kappa ξ * Complex.ofReal (Real.exp (-(QKappa ξ))) := by
  rw [tensorRep_windowAmbiguity_integral_eq_prod_oneD]
  rw [show
      (∏ q : Fin d, oneDWindowAmbiguityFactor (kappa q) (ξ.1 q) (ξ.2 q)) =
        ∏ q : Fin d,
          ((-1 : ℂ) ^ kappa q * phi1D (kappa q) (kappa q) (TKappa ξ q) *
            Complex.ofReal
              (Real.exp
                (-(((ξ.1 q) ^ 2 + (2 * Real.pi) ^ 2 * (ξ.2 q) ^ 2) / 4)))) by
    simp_all only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat]]
  exact prod_oneDWindowAmbiguity_closed_eq_PKappa_exp kappa ξ
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (ξ : PhaseSpace d) :
    ambiguityRep (varphiKappa kappa) (varphiKappa kappa) ξ =
      PKappa kappa ξ * Complex.ofReal (Real.exp (-(QKappa ξ))) := by
  let _ := hd
  rw [ambiguityRep_varphiKappa_eq_tensorRep_integral]
  apply tensorRep_windowAmbiguity_integral_eq_PKappa_exp_of_oneD
  intro q
  exact
    oneDWindowAmbiguityFactor_closed (kappa q) (ξ.1 q) (ξ.2 q)
end DimdPolyLEAN
