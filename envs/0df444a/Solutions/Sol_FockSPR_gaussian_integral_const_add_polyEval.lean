-- Prove2me | solution 1 for FockSPR.gaussian_integral_const_add_polyEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:02.146847+00:00
-- url     : https://prove2.me/submissions/a52c674d-048e-468a-ad42-cf1edb71d1de

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MainTheorem
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
public import Theorems.Thm_FockSPR_fockNorm_eq_gaussian_integral

section
@[expose] public section
open FockSPR MeasureTheory Complex Real Polynomial Finset
open scoped ENNReal ComplexConjugate
noncomputable section
namespace FockSPR
private lemma integral_addCircle_volume_eq_smul_haar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle T → E) :
    ∫ t : AddCircle T, f t = T • ∫ t : AddCircle T, f t ∂AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  rw [integral_smul_measure]
  simp [ENNReal.toReal_ofReal T_pos.le]
private lemma integral_Ioo_eq_addCircle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle T → E) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, f (QuotientAddGroup.mk θ) =
      ∫ t : AddCircle T, f t := by
  rw [← integral_Ioc_eq_integral_Ioo]
  have h : -Real.pi + T = Real.pi := by simp [T]; ring
  rw [show Set.Ioc (-Real.pi) Real.pi = Set.Ioc (-Real.pi) (-Real.pi + T) from by rw [h]]
  exact AddCircle.integral_preimage T (-Real.pi) f
private lemma integral_Ioo_eq_T_smul_haar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle T → E) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, f (QuotientAddGroup.mk θ) =
      T • ∫ t : AddCircle T, f t ∂AddCircle.haarAddCircle := by
  rw [integral_Ioo_eq_addCircle, integral_addCircle_volume_eq_smul_haar]
private lemma fourier_mk_eq_exp (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : AddCircle T) : ℂ) =
    Complex.exp (Complex.I * ↑n * ↑θ) := by
  rw [fourier_coe_apply]
  have harg : (2 * ↑π * Complex.I * ↑n * ↑θ / T : ℂ) = Complex.I * ↑n * ↑θ := by
    rw [show (T : ℂ) = (2 * Real.pi : ℝ) by simp [T]]
    field_simp [Real.pi_ne_zero]
    push_cast
    ring
  rw [harg]
private lemma cos_add_sin_mul_I (θ : ℝ) :
    (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I : ℂ) = Complex.exp (Complex.I * ↑θ) := by
  rw [mul_comm Complex.I, Complex.exp_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]
private lemma cos_add_sin_mul_I_pow (θ : ℝ) (n : ℕ) :
    (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I : ℂ) ^ n =
      Complex.exp (Complex.I * ↑(n : ℤ) * ↑θ) := by
  rw [cos_add_sin_mul_I]
  rw [show Complex.I * ↑(n : ℤ) * ↑θ = ↑n * (Complex.I * ↑θ) from by push_cast; ring]
  rw [Complex.exp_nat_mul]
private lemma polarCoord_symm_pow (r θ : ℝ) (n : ℕ) :
    (Complex.polarCoord.symm (r, θ) : ℂ) ^ n =
      (↑r) ^ n * Complex.exp (Complex.I * ↑(n : ℤ) * ↑θ) := by
  rw [Complex.polarCoord_symm_apply, mul_pow, cos_add_sin_mul_I_pow]
private lemma polyEval_polar_eq_polyEvalCircle {D : ℕ} (a : Fin D → ℂ)
    (r θ : ℝ) :
    polyEval a (Complex.polarCoord.symm (r, θ)) =
      polyEvalCircle a r (QuotientAddGroup.mk θ) := by
  rw [polyEval, polyEvalCircle]
  congr 1
  ext k
  rw [polarCoord_symm_pow, fourier_mk_eq_exp]
  ring
private lemma integral_fourier_eq_zero (n : ℤ) (hn : n ≠ 0) :
    ∫ t : AddCircle T, (fourier n) t ∂AddCircle.haarAddCircle = 0 := by
  have h : fourierCoeff (fun t => (fourier (0 : ℤ) : C(AddCircle T, ℂ)) t) (-n) = 0 := by
    rw [show (fun t => (fourier (0 : ℤ) : C(AddCircle T, ℂ)) t) =
        (fourier 0 : C(AddCircle T, ℂ)) from rfl, fourierCoeff_fourier]
    simp [Pi.single, Function.update, hn]
  rw [fourierCoeff] at h
  simp_all only [ne_eq, neg_neg, fourier_apply, zero_smul, AddCircle.toCircle_zero, Circle.coe_one,
    smul_eq_mul, mul_one]
private lemma integral_polyEvalCircle_eq_zero {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    ∫ t : AddCircle T, polyEvalCircle a r t ∂AddCircle.haarAddCircle = 0 := by
  unfold polyEvalCircle
  rw [integral_finsetSum _ (fun k _ => by
    exact
      (((fourier ((k.val + 1 : ℕ) : ℤ)) : C(AddCircle T, ℂ)).continuous.const_mul
      (a k * (r : ℂ) ^ (k.val + 1))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  apply Finset.sum_eq_zero
  intro k hk
  have hne : (((k.val + 1 : ℕ) : ℤ) ≠ 0) := by exact_mod_cast Nat.succ_ne_zero k.val
  calc
    ∫ t : AddCircle T,
        a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t
          ∂AddCircle.haarAddCircle
        = (a k * (r : ℂ) ^ (k.val + 1)) *
            ∫ t : AddCircle T, fourier ((k.val + 1 : ℕ) : ℤ) t
              ∂AddCircle.haarAddCircle := by
            exact
                                         integral_const_mul
              (a k * (r : ℂ) ^ (k.val + 1))
              (fun t : AddCircle T => (fourier ((k.val + 1 : ℕ) : ℤ) t : ℂ))
    _ = 0 := by rw [integral_fourier_eq_zero _ hne, mul_zero]
private lemma cont_integrable_circle {f : AddCircle T → ℂ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
private lemma real_cont_integrable_circle {f : AddCircle T → ℝ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
private lemma continuous_polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    Continuous (polyEvalCircle a r) := by
  unfold polyEvalCircle
  apply continuous_finsetSum
  intro k hk
  exact continuous_const.mul (fourier _).continuous
private lemma integral_re_polyEvalCircle_eq_zero {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    ∫ t : AddCircle T, (polyEvalCircle a r t).re ∂AddCircle.haarAddCircle = 0 := by
  have hint : Integrable (polyEvalCircle a r) AddCircle.haarAddCircle :=
    cont_integrable_circle (continuous_polyEvalCircle a r)
  have hre := integral_re (μ := AddCircle.haarAddCircle) (f := polyEvalCircle a r) hint
  rw [show (∫ t : AddCircle T, (polyEvalCircle a r t).re ∂AddCircle.haarAddCircle) =
    (∫ t : AddCircle T, polyEvalCircle a r t ∂AddCircle.haarAddCircle).re by exact hre]
  simp [integral_polyEvalCircle_eq_zero a r]
private lemma integral_im_polyEvalCircle_eq_zero {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    ∫ t : AddCircle T, (polyEvalCircle a r t).im ∂AddCircle.haarAddCircle = 0 := by
  have hint : Integrable (polyEvalCircle a r) AddCircle.haarAddCircle :=
    cont_integrable_circle (continuous_polyEvalCircle a r)
  have him := integral_im (μ := AddCircle.haarAddCircle) (f := polyEvalCircle a r) hint
  rw [show (∫ t : AddCircle T, (polyEvalCircle a r t).im ∂AddCircle.haarAddCircle) =
    (∫ t : AddCircle T, polyEvalCircle a r t ∂AddCircle.haarAddCircle).im by exact him]
  simp [integral_polyEvalCircle_eq_zero a r]
private lemma integral_const_add_polyEvalCircle_sq {D : ℕ}
    (a : Fin D → ℂ) (r : ℝ) (c : ℂ) :
    ∫ t : AddCircle T, ‖c + polyEvalCircle a r t‖ ^ 2
      ∂AddCircle.haarAddCircle =
      ‖c‖ ^ 2 + ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle := by
  have hcont : Continuous (polyEvalCircle a r) := continuous_polyEvalCircle a r
  have h_int1 :
      Integrable (fun t : AddCircle T => ‖c + polyEvalCircle a r t‖ ^ 2)
        AddCircle.haarAddCircle :=
    real_cont_integrable_circle ((continuous_const.add hcont).norm.pow 2)
  have h_int2 :
      Integrable (fun t : AddCircle T => ‖polyEvalCircle a r t‖ ^ 2)
        AddCircle.haarAddCircle :=
    real_cont_integrable_circle (hcont.norm.pow 2)
  have h_key : ∀ t : AddCircle T,
      ‖c + polyEvalCircle a r t‖ ^ 2 - ‖polyEvalCircle a r t‖ ^ 2 =
        ‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re + 2 * c.im * (polyEvalCircle a r t).im := by
    intro t
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sq_norm, Complex.normSq_apply]
    have hc : c.re ^ 2 + c.im ^ 2 = ‖c‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    linarith only [hc]
  have h_int3 :
      Integrable
        (fun t : AddCircle T =>
          ‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re + 2 * c.im * (polyEvalCircle a r t).im)
        AddCircle.haarAddCircle := by
    refine ((real_cont_integrable_circle continuous_const).add ?_).add ?_
    · exact real_cont_integrable_circle ((Complex.continuous_re.comp hcont).const_mul (2 * c.re))
    · exact real_cont_integrable_circle ((Complex.continuous_im.comp hcont).const_mul (2 * c.im))
  have h_diff :
      ∫ t : AddCircle T, ‖c + polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle -
      ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle = ‖c‖ ^ 2 := by
    rw [← integral_sub h_int1 h_int2]
    have h_congr :
        (fun t : AddCircle T =>
          ‖c + polyEvalCircle a r t‖ ^ 2 - ‖polyEvalCircle a r t‖ ^ 2) =
        (fun t =>
          ‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re +
            2 * c.im * (polyEvalCircle a r t).im) := by
      simp_all only []
    rw [h_congr]
    have h_split1 :
        ∫ t : AddCircle T,
            ‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re + 2 * c.im * (polyEvalCircle a r t).im
            ∂AddCircle.haarAddCircle =
          ∫ t : AddCircle T, (‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re)
            ∂AddCircle.haarAddCircle +
          ∫ t : AddCircle T, 2 * c.im * (polyEvalCircle a r t).im ∂AddCircle.haarAddCircle := by
      exact
        (integral_add
          ((real_cont_integrable_circle continuous_const).add
            (real_cont_integrable_circle ((Complex.continuous_re.comp hcont).const_mul (2 * c.re))))
          (real_cont_integrable_circle ((Complex.continuous_im.comp hcont).const_mul (2 * c.im))))
    have h_split2 :
        ∫ t : AddCircle T, (‖c‖ ^ 2 + 2 * c.re * (polyEvalCircle a r t).re)
          ∂AddCircle.haarAddCircle =
          ∫ t : AddCircle T, ‖c‖ ^ 2 ∂AddCircle.haarAddCircle +
          ∫ t : AddCircle T, 2 * c.re * (polyEvalCircle a r t).re ∂AddCircle.haarAddCircle := by
      exact
        (integral_add (real_cont_integrable_circle continuous_const)
          (real_cont_integrable_circle ((Complex.continuous_re.comp hcont).const_mul (2 * c.re))))
    rw [h_split1, h_split2]
    rw [integral_const, integral_const_mul, integral_const_mul,
      integral_re_polyEvalCircle_eq_zero, integral_im_polyEvalCircle_eq_zero]
    simp
  linarith only [h_diff]
private lemma continuous_mk_addCircle :
    Continuous (fun θ : ℝ => (QuotientAddGroup.mk θ : AddCircle T)) :=
  continuous_quotient_mk'
private lemma continuous_polyEvalCircle_comp {D : ℕ} (a : Fin D → ℂ) :
    Continuous (fun p : ℝ × ℝ => polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)) := by
  unfold polyEvalCircle
  apply continuous_finsetSum
  intro k hk
  exact Continuous.mul (Continuous.mul continuous_const
    ((continuous_ofReal.comp continuous_fst).pow _))
    ((fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ)).continuous.comp
      (continuous_mk_addCircle.comp continuous_snd))
private lemma integrable_pow_mul_exp_neg_sq (n : ℕ) :
    Integrable (fun r : ℝ => r ^ n * Real.exp (-r ^ 2)) volume := by
  have hs : (-1 : ℝ) < (n : ℝ) := by exact_mod_cast (show -1 < (n : ℤ) by omega)
  have h := integrable_rpow_mul_exp_neg_mul_sq one_pos hs
  simp_all only [rpow_natCast, neg_mul, one_mul]
private lemma integrable_abs_pow_mul_exp_neg_sq (n : ℕ) :
    Integrable (fun r : ℝ => |r| ^ n * Real.exp (-r ^ 2)) volume := by
  have :
      (fun r : ℝ => |r| ^ n * Real.exp (-r ^ 2)) =
        fun r => ‖r ^ n * Real.exp (-r ^ 2)‖ := by
    simp only [norm_mul, norm_pow, norm_eq_abs, abs_exp]
  rw [this]
  exact (integrable_pow_mul_exp_neg_sq n).norm
private lemma norm_polyEvalCircle_le {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (t : AddCircle T) :
    ‖polyEvalCircle a r t‖ ≤ ∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1) := by
  unfold polyEvalCircle
  calc
    ‖∑ k : Fin D, a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t‖
        ≤ ∑ k : Fin D, ‖a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t‖ :=
          norm_sum_le _ _
    _ ≤ ∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1) := by
          simp_all only [Nat.cast_add, Nat.cast_one, fourier_apply, fourier_add', natCast_zsmul,
            one_smul, Complex.norm_mul, norm_pow, norm_real, norm_eq_abs, Circle.norm_coe, mul_one,
            Std.le_refl]
private lemma norm_sq_polyEvalCircle_le {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (t : AddCircle T) :
    ‖polyEvalCircle a r t‖ ^ 2 ≤
      (∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1)) ^ 2 := by
  have hsumnn : 0 ≤ ∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1) := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg r) _)
  nlinarith only [norm_polyEvalCircle_le a r t, norm_nonneg (polyEvalCircle a r t)]
private lemma integrableOn_polar_norm {D : ℕ} (a : Fin D → ℂ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2))) :=
    Continuous.mul continuous_fst (Continuous.mul
      ((continuous_norm.comp (continuous_polyEvalCircle_comp a)).pow 2)
      (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
  rw [IntegrableOn, ← Measure.prod_restrict (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi)]
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  constructor
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Filter.Eventually.of_forall
    intro r hr
    have hcont_theta : Continuous (fun θ : ℝ =>
        r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2))) := by
      apply Continuous.mul continuous_const
      apply Continuous.mul
      · exact (continuous_norm.comp (continuous_finsetSum _ (fun k _ =>
          Continuous.mul (Continuous.mul continuous_const continuous_const)
            ((fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ)).continuous.comp
              continuous_mk_addCircle)))).pow 2
      · exact continuous_const
    exact (hcont_theta.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  · set C := ∑ k : Fin D, ‖a k‖
    set bound := fun r : ℝ =>
      T * (4 * C ^ 2) *
        (|r| ^ 3 * Real.exp (-r ^ 2) +
          |r| ^ (2 * D + 1) * Real.exp (-r ^ 2))
    apply Integrable.mono'
      (g := bound)
    · exact (((integrable_abs_pow_mul_exp_neg_sq 3).add
        (integrable_abs_pow_mul_exp_neg_sq (2 * D + 1))).const_mul _).restrict
    · have hcont_int : Continuous (fun r : ℝ =>
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            ‖r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
              Real.exp (-r ^ 2))‖) :=
        continuous_parametric_integral_of_continuous hcont.norm isCompact_Icc
      have hIoo_eq_Icc : ∀ r, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
            Real.exp (-r ^ 2))‖ =
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            ‖r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
              Real.exp (-r ^ 2))‖ := by
        intro r
        exact (integral_Icc_eq_integral_Ioo).symm
      simp_rw [hIoo_eq_Icc]
      exact hcont_int.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · apply (ae_restrict_iff' measurableSet_Ioi).mpr
      apply Filter.Eventually.of_forall
      intro r hr
      simp only [Set.mem_Ioi] at hr
      rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Ioo
        (fun _ _ => norm_nonneg _))]
      have hnorm_eq : ∀ y : ℝ,
          ‖(r, y).1 * (‖polyEvalCircle a (r, y).1 (↑(r, y).2)‖ ^ 2 *
            rexp (-(r, y).1 ^ 2))‖ =
          r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2)) := by
        intro y; simp only []
        rw [Real.norm_of_nonneg (mul_nonneg (le_of_lt hr)
          (mul_nonneg (sq_nonneg _) (exp_pos _).le))]
      simp_rw [hnorm_eq]
      have hr_abs : |r| = r := abs_of_pos hr
      set S := (∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1)) ^ 2 with hS_def
      have hbd : ∀ y : ℝ,
          r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2)) ≤
          r * (S * rexp (-r ^ 2)) :=
        fun y => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_sq_polyEvalCircle_le a r _)
            (exp_pos _).le) (le_of_lt hr)
      calc ∫ y in Set.Ioo (-Real.pi) Real.pi,
            r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2))
          ≤ ∫ _ in Set.Ioo (-Real.pi) Real.pi, r * (S * rexp (-r ^ 2)) := by
            apply setIntegral_mono_on
            · have hcont_y : Continuous (fun y : ℝ =>
                  r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2))) := by
                apply Continuous.mul continuous_const
                apply Continuous.mul
                · exact (continuous_norm.comp (continuous_finsetSum _ (fun k _ =>
                    Continuous.mul (Continuous.mul continuous_const continuous_const)
                      ((fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ)).continuous.comp
                        continuous_mk_addCircle)))).pow 2
                · exact continuous_const
              exact hcont_y.continuousOn.integrableOn_compact isCompact_Icc
                |>.mono_set Set.Ioo_subset_Icc_self
            · exact (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set
                Set.Ioo_subset_Icc_self
            · exact measurableSet_Ioo
            · exact fun y _ => hbd y
        _ = T * (r * (S * rexp (-r ^ 2))) := by
            rw [setIntegral_const]
            simp only [smul_eq_mul]
            rw [Measure.real, Real.volume_Ioo,
              show Real.pi - (-Real.pi) = T by simp [T]; ring,
              ENNReal.toReal_ofReal T_pos.le]
        _ ≤ bound r := by
            have hexp_pos := exp_pos (-r ^ 2)
            have hT := T_pos.le
            suffices h : r * S ≤ 4 * C ^ 2 * (r ^ 3 + r ^ (2 * D + 1)) by
              calc T * (r * (S * rexp (-r ^ 2)))
                  = T * ((r * S) * rexp (-r ^ 2)) := by ring
                _ ≤ T * (4 * C ^ 2 * (r ^ 3 + r ^ (2 * D + 1)) * rexp (-r ^ 2)) := by
                    apply mul_le_mul_of_nonneg_left _ hT
                    exact mul_le_mul_of_nonneg_right h hexp_pos.le
                _ = bound r := by
                    unfold bound
                    rw [hr_abs]
                    ring
            rw [hS_def, hr_abs]
            have hsum_factor : ∑ k : Fin D, ‖a k‖ * r ^ (k.val + 1) =
                r * ∑ k : Fin D, ‖a k‖ * r ^ k.val := by
              rw [Finset.mul_sum]
              congr 1
              ext k
              rw [pow_succ]
              ring
            rw [hsum_factor]
            ring_nf
            have hC_nn : 0 ≤ C := Finset.sum_nonneg (fun k _ => norm_nonneg (a k))
            by_cases hD : D = 0
            · subst hD
              simp
              nlinarith only [hr, sq_nonneg C, pow_nonneg (le_of_lt hr) 3]
            · have hD_pos : 0 < D := Nat.pos_of_ne_zero hD
              have hr_nn := (le_of_lt hr)
              have hpow_le : ∀ k : Fin D, r ^ k.val ≤ 1 + r ^ (D - 1) := by
                intro k
                by_cases hr1 : r ≤ 1
                · have : r ^ k.val ≤ 1 := pow_le_one₀ (n := k.val) hr_nn hr1
                  linarith only [hr_nn, this, pow_nonneg hr_nn (D - 1)]
                · push Not at hr1
                  have : r ^ k.val ≤ r ^ (D - 1) :=
                    pow_le_pow_right₀ hr1.le (by omega : k.val ≤ D - 1)
                  linarith only [this]
              have hsum_le : ∑ x : Fin D, r ^ x.val * ‖a x‖ ≤
                  (1 + r ^ (D - 1)) * C := by
                calc ∑ x, r ^ x.val * ‖a x‖
                  ≤ ∑ x : Fin D, (1 + r ^ (D - 1)) * ‖a x‖ :=
                      Finset.sum_le_sum (fun k _ =>
                        mul_le_mul_of_nonneg_right (hpow_le k) (norm_nonneg _))
                  _ = (1 + r ^ (D - 1)) * ∑ x : Fin D, ‖a x‖ := by
                    simpa using (Finset.mul_sum (s := Finset.univ)
                      (a := 1 + r ^ (D - 1)) (f := fun x : Fin D => ‖a x‖)).symm
                  _ = _ := by simp [C]
              have hsum_nn : 0 ≤ ∑ x : Fin D, r ^ x.val * ‖a x‖ :=
                Finset.sum_nonneg (fun k _ =>
                  mul_nonneg (pow_nonneg hr_nn k.val) (norm_nonneg _))
              have hfact_nn : 0 ≤ (1 + r ^ (D - 1)) * C :=
                mul_nonneg (by linarith only [hr_nn, pow_nonneg hr_nn (D - 1)]) hC_nn
              have hsq : (∑ x : Fin D, r ^ x.val * ‖a x‖) ^ 2 ≤
                  ((1 + r ^ (D - 1)) * C) ^ 2 :=
                sq_le_sq' (by linarith only [hsum_le, hsum_nn]) hsum_le
              have hsq2 : ((1 + r ^ (D - 1)) * C) ^ 2 ≤
                  2 * (1 + (r ^ (D - 1)) ^ 2) * C ^ 2 := by
                    nlinarith only [sq_nonneg (1 - r ^ (D - 1))]
              have hpow_eq : r ^ 3 * (r ^ (D - 1)) ^ 2 = r * r ^ (D * 2) := by
                have hexp_eq : 3 + (D - 1) * 2 = 1 + D * 2 := by omega
                rw [← pow_mul, ← pow_add, hexp_eq, pow_add, pow_one]
              calc r ^ 3 * (∑ x, r ^ x.val * ‖a x‖) ^ 2
                  ≤ r ^ 3 * (2 * (1 + (r ^ (D - 1)) ^ 2) * C ^ 2) := by
                    exact mul_le_mul_of_nonneg_left
                      (le_trans hsq hsq2) (pow_nonneg hr_nn 3)
                _ = 2 * C ^ 2 * (r ^ 3 + r ^ 3 * (r ^ (D - 1)) ^ 2) := by ring
                _ = 2 * C ^ 2 * (r ^ 3 + r * r ^ (D * 2)) := by rw [hpow_eq]
                _ ≤ r * r ^ (D * 2) * C ^ 2 * 4 + r ^ 3 * C ^ 2 * 4 := by
                    nlinarith only [pow_nonneg hr_nn 3, mul_nonneg hr_nn (pow_nonneg hr_nn (D * 2))]
private lemma norm_add_sq_le (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := parallelogram_law_with_norm ℂ a b
  nlinarith only [h, sq_abs (‖a + b‖), sq_abs (‖a - b‖), sq_abs (‖a‖), sq_abs (‖b‖)]
private lemma integrableOn_polar_const (u : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ => p.1 * (u ^ 2 * Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  have hcont : Continuous (fun p : ℝ × ℝ => p.1 * (u ^ 2 * Real.exp (-p.1 ^ 2))) :=
    Continuous.mul continuous_fst
      (Continuous.mul continuous_const
        (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
  rw [IntegrableOn, ← Measure.prod_restrict (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi)]
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  constructor
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Filter.Eventually.of_forall
    intro r hr
    have hcont_theta : Continuous (fun θ : ℝ => r * (u ^ 2 * Real.exp (-r ^ 2))) := by continuity
    exact (hcont_theta.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  · set bound := fun r : ℝ => T * (u ^ 2 * (|r| ^ 1 * Real.exp (-r ^ 2)))
    have hbound_def : bound = fun r : ℝ => (T * u ^ 2) * (|r| ^ 1 * Real.exp (-r ^ 2)) := by
      funext r
      unfold bound
      ring
    apply Integrable.mono'
      (g := bound)
    · rw [hbound_def]
      exact ((integrable_abs_pow_mul_exp_neg_sq 1).const_mul (T * u ^ 2)).restrict
    · have hcont_int : Continuous (fun r : ℝ =>
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            ‖r * (u ^ 2 * Real.exp (-r ^ 2))‖) :=
        continuous_parametric_integral_of_continuous hcont.norm isCompact_Icc
      have hIoo_eq_Icc : ∀ r, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖r * (u ^ 2 * Real.exp (-r ^ 2))‖ =
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
            ‖r * (u ^ 2 * Real.exp (-r ^ 2))‖ := by
        simp_all
      simp_rw [hIoo_eq_Icc]
      exact hcont_int.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · apply (ae_restrict_iff' measurableSet_Ioi).mpr
      apply Filter.Eventually.of_forall
      intro r hr
      simp only [Set.mem_Ioi] at hr
      rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Ioo
        (fun _ _ => norm_nonneg _))]
      have hnorm_eq : ∀ y : ℝ,
          ‖(r, y).1 * (u ^ 2 * Real.exp (-(r, y).1 ^ 2))‖ =
            r * (u ^ 2 * Real.exp (-r ^ 2)) := by
        intro y
        rw [Real.norm_of_nonneg]
        exact mul_nonneg (le_of_lt hr) (mul_nonneg (sq_nonneg u) (le_of_lt (Real.exp_pos _)))
      rw [setIntegral_congr_fun measurableSet_Ioo (by
        intro y hy
        exact hnorm_eq y)]
      have hnn :
          0 ≤ r * (u ^ 2 * Real.exp (-r ^ 2)) :=
        mul_nonneg (le_of_lt hr) (mul_nonneg (sq_nonneg u) (le_of_lt (Real.exp_pos _)))
      calc
        ∫ θ in Set.Ioo (-Real.pi) Real.pi, r * (u ^ 2 * Real.exp (-r ^ 2))
            = T * (r * (u ^ 2 * Real.exp (-r ^ 2))) := by
                rw [setIntegral_const]
                simp only [smul_eq_mul]
                rw [Measure.real, Real.volume_Ioo,
                  show Real.pi - (-Real.pi) = T by simp [T]; ring,
                  ENNReal.toReal_ofReal T_pos.le]
        _ ≤ bound r := by
            unfold bound
            rw [abs_of_pos hr]
            ring_nf
            exact le_rfl
private lemma integrableOn_polar_const_add {D : ℕ} (a : Fin D → ℂ) (c : ℂ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  rw [IntegrableOn]
  let μ : Measure (ℝ × ℝ) :=
    (volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
  have hconst :
      Integrable (fun p : ℝ × ℝ => p.1 * (‖c‖ ^ 2 * Real.exp (-p.1 ^ 2))) μ :=
    integrableOn_polar_const ‖c‖
  have hnorm :
      Integrable (fun p : ℝ × ℝ =>
        p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2))) μ := integrableOn_polar_norm a
  set g : ℝ × ℝ → ℝ := fun p =>
    2 * (p.1 * (‖c‖ ^ 2 * Real.exp (-p.1 ^ 2))) +
      2 * (p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2)))
  have hg : Integrable g μ := by
    refine (hconst.const_mul 2).add ?_
    exact hnorm.const_mul 2
  have hcont : Continuous (fun p : ℝ × ℝ =>
      p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2))) :=
    Continuous.mul continuous_fst (Continuous.mul
      ((continuous_const.add (continuous_polyEvalCircle_comp a)).norm.pow 2)
      (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
  refine Integrable.mono' hg ?_ ?_
  · exact hcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · apply (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioo)).mpr
    apply Filter.Eventually.of_forall
    intro p hp
    rcases hp with ⟨hr, hθ⟩
    simp only [Set.mem_Ioi, Set.mem_Ioo] at hr hθ
    rw [Real.norm_of_nonneg]
    · set q := polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)
      have hbase : ‖c + q‖ ^ 2 ≤ 2 * ‖c‖ ^ 2 + 2 * ‖q‖ ^ 2 := by simpa [q] using norm_add_sq_le c q
      have hmul :
          p.1 * (‖c + q‖ ^ 2 * Real.exp (-p.1 ^ 2))
            ≤ p.1 * ((2 * ‖c‖ ^ 2 + 2 * ‖q‖ ^ 2) * Real.exp (-p.1 ^ 2)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbase (le_of_lt (Real.exp_pos _)))
          (le_of_lt hr)
      calc
        p.1 * (‖c + q‖ ^ 2 * Real.exp (-p.1 ^ 2))
            ≤ p.1 * ((2 * ‖c‖ ^ 2 + 2 * ‖q‖ ^ 2) * Real.exp (-p.1 ^ 2)) := hmul
        _ = g p := by
            unfold g q
            ring
    · exact mul_nonneg (le_of_lt hr)
        (mul_nonneg (sq_nonneg ‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖)
          (le_of_lt (Real.exp_pos _)))
private lemma radial_gaussian_integral (n : ℕ) :
    2 * ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-r ^ 2) =
      (n.factorial : ℝ) := by
  have hp : (0 : ℝ) < 2 := two_pos
  have hq : (-1 : ℝ) < (2 * (n : ℝ) + 1) := by linarith only [Nat.cast_nonneg (α := ℝ) n]
  have pow_eq : ∀ (r : ℝ), r ∈ Set.Ioi (0 : ℝ) →
      r ^ (2 * n + 1) * Real.exp (-r ^ 2) =
      r ^ (2 * (n : ℝ) + 1) * Real.exp (-r ^ (2 : ℝ)) := by
    intro r _
    congr 1
    · rw [← rpow_natCast r (2 * n + 1)]
      simp_all only [Nat.ofNat_pos, Set.mem_Ioi, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one]
    · simp_all only [Nat.ofNat_pos, Set.mem_Ioi, rpow_ofNat]
  rw [setIntegral_congr_fun measurableSet_Ioi pow_eq]
  rw [integral_rpow_mul_exp_neg_rpow hp hq]
  have h1 : (2 * (n : ℝ) + 1 + 1) / 2 = ↑n + 1 := by ring
  rw [h1, Real.Gamma_nat_eq_factorial]
  ring
private lemma norm_polyEval_eq_norm_polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r θ : ℝ) :
    ‖polyEval a (Complex.polarCoord.symm (r, θ))‖ =
      ‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ := by rw [polyEval_polar_eq_polyEvalCircle]
private lemma fockNorm_polar_local {D : ℕ} (a : Fin D → ℂ) :
    (1 / Real.pi) * ∫ z : ℂ, ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
    2 * ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
        ∂AddCircle.haarAddCircle) := by
  rw [show (∫ z : ℂ, ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) =
    (∫ p in polarCoord.target, p.1 • (‖polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
      Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2))
    ) from (Complex.integral_comp_polarCoord_symm _).symm]
  rw [polarCoord_target]
  have integrand_rw : ∀ p : ℝ × ℝ,
      p.1 • (‖polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
        Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2)) =
      p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2)) := by
    intro ⟨r, θ⟩
    simp only [smul_eq_mul, norm_polyEval_eq_norm_polyEvalCircle, Complex.norm_polarCoord_symm,
      sq_abs]
  simp_rw [integrand_rw]
  have hint := integrableOn_polar_norm a
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod _ hint]
  simp only []
  have inner_eq : ∀ r : ℝ,
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2))) =
      T * (r * Real.exp (-r ^ 2) *
        ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    intro r
    have h1 : ∀ θ : ℝ,
        r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2)) =
          (r * Real.exp (-r ^ 2)) *
            ‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 := by
      intro θ
      ring
    simp_rw [h1]
    rw [MeasureTheory.integral_const_mul]
    have := integral_Ioo_eq_T_smul_haar (fun t : AddCircle T =>
      ‖polyEvalCircle a r t‖ ^ 2)
    simp only [smul_eq_mul] at this
    rw [show (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2) =
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (fun t : AddCircle T => ‖polyEvalCircle a r t‖ ^ 2) (QuotientAddGroup.mk θ))
        from by rfl]
    rw [this]
    ring
  simp_rw [inner_eq]
  rw [MeasureTheory.integral_const_mul]
  have hT_eq : (1 / Real.pi) * T = 2 := by
    simp only [T]
    field_simp
  rw [← mul_assoc, hT_eq]
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open FockSPR MeasureTheory Complex Real Polynomial Finset
open scoped ENNReal ComplexConjugate
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution {D : ℕ} (a : Fin D → ℂ) (c : ℂ) :
    (1 / Real.pi) * ∫ z : ℂ, ‖c + polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      ‖c‖ ^ 2 + fockNormSq a := by
  rw [show (∫ z : ℂ, ‖c + polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) =
    (∫ p in polarCoord.target, p.1 • (‖c + polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
      Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2))
    ) from (Complex.integral_comp_polarCoord_symm _).symm]
  rw [polarCoord_target]
  have integrand_rw : ∀ p : ℝ × ℝ,
      p.1 • (‖c + polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
        Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2)) =
      p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2)) := by
    intro ⟨r, θ⟩
    simp only [smul_eq_mul, polyEval_polar_eq_polyEvalCircle, Complex.norm_polarCoord_symm, sq_abs]
  simp_rw [integrand_rw]
  have hint : IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := integrableOn_polar_const_add a c
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod _ hint]
  simp only []
  have inner_eq : ∀ r : ℝ,
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * (‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2))) =
      T * (r * Real.exp (-r ^ 2) *
        ∫ t : AddCircle T, ‖c + polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    intro r
    have h1 : ∀ θ : ℝ,
        r * (‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2)) =
          (r * Real.exp (-r ^ 2)) *
            ‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 := by
      intro θ
      ring
    simp_rw [h1]
    rw [MeasureTheory.integral_const_mul]
    have := integral_Ioo_eq_T_smul_haar (fun t : AddCircle T =>
      ‖c + polyEvalCircle a r t‖ ^ 2)
    simp only [smul_eq_mul] at this
    rw [show (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2) =
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (fun t : AddCircle T => ‖c + polyEvalCircle a r t‖ ^ 2)
            (QuotientAddGroup.mk θ))
        from by rfl]
    rw [this]
    ring
  simp_rw [inner_eq, integral_const_add_polyEvalCircle_sq]
  set whole : ℝ → ℝ := fun r =>
    T * (r * Real.exp (-r ^ 2) *
      (‖c‖ ^ 2 + ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle))
  set first : ℝ → ℝ := fun r => T * (r * Real.exp (-r ^ 2) * ‖c‖ ^ 2)
  set second : ℝ → ℝ := fun r =>
    T * (r * Real.exp (-r ^ 2) *
      ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle)
  have hwhole_eq : whole = fun r : ℝ =>
      ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * (‖c + polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
          Real.exp (-r ^ 2)) := by
    funext r
    rw [inner_eq]
    unfold whole
    rw [integral_const_add_polyEvalCircle_sq]
  have hwhole_int : Integrable whole (volume.restrict (Set.Ioi 0)) := by
    have hcont_add : Continuous (fun p : ℝ × ℝ =>
        p.1 * (‖c + polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
          Real.exp (-p.1 ^ 2))) :=
      Continuous.mul continuous_fst (Continuous.mul
        ((continuous_const.add (continuous_polyEvalCircle_comp a)).norm.pow 2)
        (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
    have hint' := integrableOn_polar_const_add a c
    rw [IntegrableOn, ← Measure.prod_restrict (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi)] at hint'
    rw [integrable_prod_iff hcont_add.aestronglyMeasurable] at hint'
    refine hint'.2.congr ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with r hr
    have hnorm_eq : ∀ y : ℝ,
        ‖(r, y).1 * (‖c + polyEvalCircle a (r, y).1 (↑(r, y).2)‖ ^ 2 *
          Real.exp (-(r, y).1 ^ 2))‖ =
          r * (‖c + polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 *
            Real.exp (-r ^ 2)) := by
      intro y
      rw [Real.norm_of_nonneg]
      exact mul_nonneg (le_of_lt hr)
        (mul_nonneg (sq_nonneg ‖c + polyEvalCircle a r (QuotientAddGroup.mk y)‖)
          (le_of_lt (Real.exp_pos _)))
    rw [setIntegral_congr_fun measurableSet_Ioo (by
      intro y hy
      exact hnorm_eq y)]
    exact (congrFun hwhole_eq r).symm
  have hfirst_int : Integrable first (volume.restrict (Set.Ioi 0)) := by
    unfold first
    have : IntegrableOn (fun r : ℝ => (T * ‖c‖ ^ 2) * (r ^ 1 * Real.exp (-r ^ 2)))
        (Set.Ioi 0) volume := (integrable_pow_mul_exp_neg_sq 1).integrableOn.const_mul (T * ‖c‖ ^ 2)
    simpa only [mul_comm, mul_left_comm, IntegrableOn, pow_one, mul_assoc] using this
  have hsum : whole = first + second := by
    funext r
    simp [whole, first, second]
    ring
  have hsecond_int : Integrable second (volume.restrict (Set.Ioi 0)) := by
    rw [show second = whole - first by
      funext r
      simp [whole, first, second]
      ring]
    exact hwhole_int.sub hfirst_int
  rw [show (∫ r in Set.Ioi (0 : ℝ), whole r) =
      ∫ r in Set.Ioi (0 : ℝ), (first + second) r by rw [hsum]]
  rw [show (∫ r in Set.Ioi (0 : ℝ), (first + second) r) =
      ∫ r in Set.Ioi (0 : ℝ), first r + second r by rfl]
  rw [integral_add hfirst_int hsecond_int]
  have hfirst_eval :
      (1 / Real.pi) * ∫ r in Set.Ioi (0 : ℝ), first r = ‖c‖ ^ 2 := by
    unfold first
    rw [show (fun r : ℝ => T * (r * Real.exp (-r ^ 2) * ‖c‖ ^ 2)) =
      fun r => (T * (r * Real.exp (-r ^ 2))) * ‖c‖ ^ 2 by
        ext r
        ring]
    rw [MeasureTheory.integral_mul_const]
    have hT_eq : (1 / Real.pi) * T = 2 := by
      simp only [T]
      field_simp
    have hrad : 2 * ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) = 1 := by
      simpa only [mul_zero, zero_add, pow_one, Nat.factorial_zero, Nat.cast_one] using
        radial_gaussian_integral 0
    calc
      (1 / Real.pi) * ((∫ r in Set.Ioi (0 : ℝ), T * (r * Real.exp (-r ^ 2)) ∂volume) * ‖c‖ ^ 2)
          = (((1 / Real.pi) * T) *
            (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) ∂volume)) * ‖c‖ ^ 2 := by
              rw [integral_const_mul]
              ring
      _ = 2 * (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) ∂volume) * ‖c‖ ^ 2 := by rw [hT_eq]
      _ = ‖c‖ ^ 2 := by nlinarith only [hrad]
  have hsecond_eval :
      (1 / Real.pi) * ∫ r in Set.Ioi (0 : ℝ), second r = fockNormSq a := by
    unfold second
    rw [MeasureTheory.integral_const_mul]
    have hT_eq : (1 / Real.pi) * T = 2 := by
      simp only [T]
      field_simp
    calc
      (1 / Real.pi) * (T * ∫ r in Set.Ioi (0 : ℝ),
          r * Real.exp (-r ^ 2) *
            ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle)
          = ((1 / Real.pi) * T) *
              ∫ r in Set.Ioi (0 : ℝ),
                r * Real.exp (-r ^ 2) *
                  ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
                    ∂AddCircle.haarAddCircle := by ring
      _ = 2 * ∫ r in Set.Ioi (0 : ℝ),
            r * Real.exp (-r ^ 2) *
              ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2
                ∂AddCircle.haarAddCircle := by rw [hT_eq]
      _ = (1 / Real.pi) * ∫ z : ℂ, ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
            simpa only [one_div] using (fockNorm_polar_local a).symm
      _ = fockNormSq a := fockNorm_eq_gaussian_integral a
  have hfinal :
      (1 / Real.pi) * (∫ r in Set.Ioi (0 : ℝ), first r) +
        (1 / Real.pi) * ∫ r in Set.Ioi (0 : ℝ), second r = ‖c‖ ^ 2 + fockNormSq a := by
    rw [hfirst_eval, hsecond_eval]
  have hparen2 :
      (1 / Real.pi) *
          ((∫ r in Set.Ioi (0 : ℝ), first r) +
            ∫ r in Set.Ioi (0 : ℝ), second r) =
        (1 / Real.pi) * (∫ r in Set.Ioi (0 : ℝ), first r) +
          (1 / Real.pi) * ∫ r in Set.Ioi (0 : ℝ), second r := by ring
  exact hparen2.trans hfinal
end FockSPR
