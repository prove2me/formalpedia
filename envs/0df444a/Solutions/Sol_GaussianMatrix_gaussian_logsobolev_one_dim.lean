-- Prove2me | solution 1 for GaussianMatrix.gaussian_logsobolev_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:13:24.708009+00:00
-- url     : https://prove2.me/submissions/f845f836-1664-4904-ac7a-a4b032bcba3c

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

/-!
# Gross's Gaussian logarithmic Sobolev inequality in dimension one

Self-contained proof via the Ornstein–Uhlenbeck semigroup
`P_t g(x) = ∫ g(e^{-t} x + √(1-e^{-2t}) y) dγ(y)`:

1. `ou_semigroup_invariant`: `∫ P_t h dγ = ∫ h dγ` (`γ ⊗ γ` pushed forward by a rotation).
2. `ou_semigroup_commutation`: `(P_t f)' = e^{-t} P_t f'`.
3. `gaussian_ibp_one_dim`: `∫ x h(x) dγ = ∫ h' dγ`.
4. `ou_entropy_hasDerivAt`: `d/dt ∫ P_t f log P_t f dγ = -∫ ((P_t f)')² / P_t f dγ` for `t > 0`.
5. `gaussian_logsobolev_bounded_below`: `Ent(f) ≤ ½ ∫ f'²/f` for `δ ≤ f ≤ C`, `|f'| ≤ C`
   (monotonicity of `Ent(P_t f) - ½ e^{-2t} ∫ f'²/f`, Cauchy–Schwarz and invariance).
6. `gaussian_logsobolev_one_dim_compact_support`: apply 5 to `g² + ε`, let `ε → 0`.
7. Main theorem: truncate `g` by smooth cutoffs and pass to the limit (dominated convergence).
-/


/-! ## `ou_semigroup_invariant` -/

namespace GaussianMatrix

/-- The image of `γ ⊗ γ` under `(x, y) ↦ a x + b y` is `γ` when `a² + b² = 1`. -/
lemma map_lin_comb_gaussian (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      = gaussianReal 0 1 := by
  have h1 : (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (fun x => a * x) (fun y => b * y) := by
    ext p; simp
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  rw [← Measure.conv, gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · apply NNReal.eq; simp [hab]

lemma integral_lin_comb_gaussian (h : ℝ → ℝ) (hh : Integrable h (gaussianReal 0 1)) (a b : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    ∫ x, (∫ y, h (a * x + b * y) ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ x, h x ∂(gaussianReal 0 1) := by
  have hmap : ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => a * p.1 + b * p.2) = gaussianReal 0 1 := by
    exact map_lin_comb_gaussian a b hab
  have hF : AEMeasurable (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by fun_prop
  have hh' : Integrable h (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => a * p.1 + b * p.2)) := by rw [hmap]; exact hh
  have hcomp : Integrable (fun p : ℝ × ℝ => h (a * p.1 + b * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (integrable_map_measure hh'.aestronglyMeasurable hF).1 hh'
  rw [← integral_prod (fun p : ℝ × ℝ => h (a * p.1 + b * p.2)) hcomp]
  rw [← integral_map hF (by rw [hmap]; exact hh.aestronglyMeasurable), hmap]

end GaussianMatrix

open GaussianMatrix

theorem GaussianMatrix.ou_semigroup_invariant (h : ℝ → ℝ) (hh : Integrable h (gaussianReal 0 1)) (t : ℝ)
    (ht : 0 ≤ t) :
    ∫ x, (∫ y, h (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ x, h x ∂(gaussianReal 0 1) := by
  apply integral_lin_comb_gaussian h hh
  have h1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [Real.sq_sqrt (by linarith), sq, ← Real.exp_add]
  ring_nf

/-! ## `ou_semigroup_commutation` -/

namespace GaussianMatrix

lemma integrable_abs_id_gaussian : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
  have : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)
  exact this.abs

/-- A function with bounded derivative has linear growth. -/
lemma abs_le_of_deriv_bound (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (z : ℝ) : |f z| ≤ |f 0| + C * |z| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.univ) (C := C)
    (fun x _ => hf x) (fun x _ => by simpa using hdf x) convex_univ (Set.mem_univ 0)
    (Set.mem_univ z)
  simp only [Real.norm_eq_abs, sub_zero] at this
  have h2 := abs_sub_abs_le_abs_sub (f z) (f 0)
  linarith

lemma integrable_comp_affine_of_deriv_bound (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (c d : ℝ) :
    Integrable (fun y => f (c + d * y)) (gaussianReal 0 1) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hdf 0)
  refine Integrable.mono' ((integrable_const (|f 0| + C * |c|)).add
    (integrable_abs_id_gaussian.const_mul (C * |d|))) ?_ ?_
  · exact (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_le_of_deriv_bound f hf C hdf _).trans ?_
    have : |c + d * y| ≤ |c| + |d| * |y| := by
      rw [← abs_mul]; exact abs_add_le _ _
    simp only [Pi.add_apply]
    nlinarith

end GaussianMatrix

open GaussianMatrix

theorem GaussianMatrix.ou_semigroup_commutation (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (t x : ℝ) :
    HasDerivAt
      (fun z => ∫ y, f (Real.exp (-t) * z + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1))
      (Real.exp (-t) * ∫ y, deriv f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) x := by
  set a := Real.exp (-t)
  set b := Real.sqrt (1 - Real.exp (-(2 * t)))
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  rw [← integral_const_mul]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun z y => f (a * z + b * y)) (F' := fun z y => a * deriv f (a * z + b * y))
    (x₀ := x) (bound := fun _ => |a| * C) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall (fun z =>
      (hfd.continuous.comp (by fun_prop)).aestronglyMeasurable)
  · exact integrable_comp_affine_of_deriv_bound f hfd C hdf (a * x) b
  · exact ((hfc.comp (by fun_prop)).const_mul a).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y z _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hdf _) (abs_nonneg _)
  · exact integrable_const _
  · refine Filter.Eventually.of_forall (fun y z _ => ?_)
    have h1 : HasDerivAt (fun z => a * z + b * y) a z := by
      simpa using ((hasDerivAt_id z).const_mul a).add_const (b * y)
    have := (hfd (a * z + b * y)).hasDerivAt.comp z h1
    rw [mul_comm (deriv f _) a] at this
    exact this

/-! ## `gaussian_ibp_one_dim` -/

namespace GaussianMatrix

lemma integrable_gaussian_iff (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [smul_eq_mul]

lemma integrable_abs_id_gaussian' : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
  have : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)
  exact this.abs

lemma integrable_sq_id_gaussian : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_pow (by norm_num)
  simpa using this

lemma abs_le_of_deriv_bound' (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (z : ℝ) : |f z| ≤ |f 0| + C * |z| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.univ) (C := C)
    (fun x _ => hf x) (fun x _ => by simpa using hdf x) convex_univ (Set.mem_univ 0)
    (Set.mem_univ z)
  simp only [Real.norm_eq_abs, sub_zero] at this
  have h2 := abs_sub_abs_le_abs_sub (f z) (f 0)
  linarith

lemma gaussianPDFReal_zero_one_eq :
    gaussianPDFReal 0 1 = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  funext x; simp [gaussianPDFReal_def]

lemma hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(x * gaussianPDFReal 0 1 x)) x := by
  rw [gaussianPDFReal_zero_one_eq]
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-x) x :=
    (((hasDerivAt_pow 2 x).neg).div_const 2).congr_deriv (by norm_num; ring)
  exact ((h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹).congr_deriv (by ring)

end GaussianMatrix

open GaussianMatrix

theorem GaussianMatrix.gaussian_ibp_one_dim (h : ℝ → ℝ) (hh : Differentiable ℝ h) (C : ℝ)
    (hdh : ∀ x, |deriv h x| ≤ C) :
    ∫ x, x * h x ∂(gaussianReal 0 1) = ∫ x, deriv h x ∂(gaussianReal 0 1) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hdh 0)
  set φ := gaussianPDFReal 0 1
  have hhc : Continuous h := hh.continuous
  -- integrability facts under γ
  have hxh : Integrable (fun x => x * h x) (gaussianReal 0 1) := by
    refine Integrable.mono' ((integrable_abs_id_gaussian'.const_mul |h 0|).add
      (integrable_sq_id_gaussian.const_mul C)) (by fun_prop) ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := abs_le_of_deriv_bound' h hh C hdh x
    have hx := abs_nonneg x
    simp only [Pi.add_apply]
    rw [← sq_abs x]
    nlinarith
  have hdm : Measurable (deriv h) := measurable_deriv h
  have hdi : Integrable (deriv h) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const C) hdm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hdh x)
  have hhi : Integrable h (gaussianReal 0 1) := by
    refine Integrable.mono' ((integrable_const |h 0|).add
      (integrable_abs_id_gaussian'.const_mul C)) hhc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]; exact abs_le_of_deriv_bound' h hh C hdh x)
  rw [integrable_gaussian_iff] at hxh hdi hhi
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  -- integration by parts on the line with `u = h`, `v = -φ`, `v' = x φ`
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h) (v := fun x => -φ x)
    (u' := deriv h) (v' := fun x => x * φ x)
    (fun x _ => (hh x).hasDerivAt)
    (fun x _ => ((hasDerivAt_gaussianPDFReal_zero_one x).neg).congr_deriv (by ring))
    (by
      have : (h * fun x => x * φ x) = fun x => φ x * (x * h x) := by funext x; simp; ring
      rw [this]; exact hxh)
    (by
      have : (deriv h * fun x => -φ x) = fun x => -(φ x * deriv h x) := by funext x; simp; ring
      rw [this]; exact hdi.neg)
    (by
      have : (h * fun x => -φ x) = fun x => -(φ x * h x) := by funext x; simp; ring
      rw [this]; exact hhi.neg)
  have e1 : (fun x => φ x * (x * h x)) = fun x => h x * (x * φ x) := by funext x; ring
  have e2 : (fun x => φ x * deriv h x) = fun x => -(deriv h x * -φ x) := by funext x; ring
  rw [e1, key, e2, integral_neg]

/-! ## `ou_entropy_hasDerivAt` -/

set_option linter.unusedSectionVars false

namespace GaussianMatrix

open Filter Topology Set

/-- `√(1 - e^{-2s})`, the noise coefficient of the Ornstein–Uhlenbeck semigroup. -/
noncomputable def ouB (s : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-(2 * s)))

/-- The one-dimensional Ornstein–Uhlenbeck semigroup (Mehler formula). -/
noncomputable def ouP (t : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, h (Real.exp (-t) * x + ouB t * y) ∂(gaussianReal 0 1)

lemma ouB_pos {s : ℝ} (hs : 0 < s) : 0 < ouB s := by
  unfold ouB
  apply Real.sqrt_pos.2
  have : Real.exp (-(2 * s)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

lemma ouB_sq {s : ℝ} (hs : 0 ≤ s) : ouB s ^ 2 = 1 - Real.exp (-(2 * s)) := by
  unfold ouB
  have : Real.exp (-(2 * s)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [Real.sq_sqrt (by linarith)]

lemma ouB_mono {s₁ s₂ : ℝ} (h : s₁ ≤ s₂) : ouB s₁ ≤ ouB s₂ := by
  unfold ouB
  apply Real.sqrt_le_sqrt
  have : Real.exp (-(2 * s₂)) ≤ Real.exp (-(2 * s₁)) := Real.exp_le_exp.2 (by linarith)
  linarith

lemma hasDerivAt_ouB {s : ℝ} (hs : 0 < s) :
    HasDerivAt ouB (Real.exp (-(2 * s)) / ouB s) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(2 * s))) (2 * Real.exp (-(2 * s))) s := by
    have := (((hasDerivAt_id s).const_mul 2).neg.exp).const_sub 1
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply, id]; ring
  have hne : 1 - Real.exp (-(2 * s)) ≠ 0 := by
    have : Real.exp (-(2 * s)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have := h1.sqrt hne
  refine this.congr_deriv ?_
  unfold ouB
  have hb : 0 < Real.sqrt (1 - Real.exp (-(2 * s))) := Real.sqrt_pos.2 (by
    have : Real.exp (-(2 * s)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith)
  field_simp

lemma ouB_sq_eq_exp {s : ℝ} : Real.exp (-s) ^ 2 = Real.exp (-(2 * s)) := by
  rw [sq, ← Real.exp_add]; ring_nf

/-! ### Integrability under `γ` -/

lemma integrable_abs_y : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) :=
  (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)).abs

lemma integrable_bdd_comp (k : ℝ → ℝ) (hk : Measurable k) (B : ℝ) (hB : ∀ z, |k z| ≤ B)
    (c d : ℝ) : Integrable (fun y => k (c + d * y)) (gaussianReal 0 1) :=
  Integrable.mono' (integrable_const B) (hk.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hB _))

lemma integrable_bdd_comp_affine (k : ℝ → ℝ) (hk : Measurable k) (B : ℝ) (hB : ∀ z, |k z| ≤ B)
    (c d e g : ℝ) :
    Integrable (fun y => k (c + d * y) * (e + g * y)) (gaussianReal 0 1) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine Integrable.mono' ((integrable_const (B * |e|)).add
    (integrable_abs_y.const_mul (B * |g|)))
    ((hk.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall (fun y => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |e + g * y| ≤ |e| + |g| * |y| := by rw [← abs_mul]; exact abs_add_le _ _
  have h2 := hB (c + d * y)
  simp only [Pi.add_apply]
  calc |k (c + d * y)| * |e + g * y| ≤ B * (|e| + |g| * |y|) :=
        mul_le_mul h2 h1 (abs_nonneg _) hB0
    _ = B * |e| + B * |g| * |y| := by ring

lemma integrable_y_mul_bdd_comp (k : ℝ → ℝ) (hk : Measurable k) (B : ℝ) (hB : ∀ z, |k z| ≤ B)
    (c d : ℝ) : Integrable (fun y => y * k (c + d * y)) (gaussianReal 0 1) := by
  have := integrable_bdd_comp_affine k hk B hB c d 0 1
  refine this.congr (Eventually.of_forall (fun y => ?_))
  simp only; ring

/-! ### Time derivative of the semigroup at a point -/

/-- The `t`-derivative of the integrand. -/
lemma hasDerivAt_integrand_time (f : ℝ → ℝ) (hfd : Differentiable ℝ f) (x y s : ℝ)
    (hs : 0 < s) :
    HasDerivAt (fun s => f (Real.exp (-s) * x + ouB s * y))
      (deriv f (Real.exp (-s) * x + ouB s * y)
        * (-Real.exp (-s) * x + Real.exp (-(2 * s)) / ouB s * y)) s := by
  have h1 : HasDerivAt (fun s => Real.exp (-s) * x + ouB s * y)
      (-Real.exp (-s) * x + Real.exp (-(2 * s)) / ouB s * y) s := by
    have ha : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s := by
      have := (hasDerivAt_id s).neg.exp
      refine this.congr_deriv ?_
      simp only [Pi.neg_apply, id]; ring
    exact (ha.mul_const x).add ((hasDerivAt_ouB hs).mul_const y)
  exact (hfd _).hasDerivAt.comp s h1

/-- The time derivative of `s ↦ P_s f(x)` at `s₀ > 0`. -/
lemma hasDerivAt_ouP_time (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ)
    (hfb : ∀ z, |f z| ≤ C) (hdf : ∀ z, |deriv f z| ≤ C) (x s₀ : ℝ) (hs₀ : 0 < s₀) :
    HasDerivAt (fun s => ouP s f x)
      (∫ y, deriv f (Real.exp (-s₀) * x + ouB s₀ * y)
        * (-Real.exp (-s₀) * x + Real.exp (-(2 * s₀)) / ouB s₀ * y) ∂(gaussianReal 0 1)) s₀ := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hC : 0 ≤ C := (abs_nonneg _).trans (hfb 0)
  set K := 1 / ouB (s₀ / 2) with hK
  have hb0 : 0 < ouB (s₀ / 2) := ouB_pos (by linarith)
  have hball : ∀ s ∈ Metric.ball s₀ (s₀ / 2), 0 < s ∧ |Real.exp (-s)| ≤ 1 ∧
      |Real.exp (-(2 * s)) / ouB s| ≤ K := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs1 : s₀ / 2 < s := by linarith
    have hspos : 0 < s := by linarith
    refine ⟨hspos, ?_, ?_⟩
    · rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.2 (by linarith)
    · have hbs : ouB (s₀ / 2) ≤ ouB s := ouB_mono hs1.le
      rw [abs_of_pos (div_pos (Real.exp_pos _) (ouB_pos hspos)), hK,
        div_le_div_iff₀ (ouB_pos hspos) hb0]
      have : Real.exp (-(2 * s)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      nlinarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun s y => f (Real.exp (-s) * x + ouB s * y))
    (F' := fun s y => deriv f (Real.exp (-s) * x + ouB s * y)
        * (-Real.exp (-s) * x + Real.exp (-(2 * s)) / ouB s * y))
    (x₀ := s₀) (bound := fun y => C * (|x| + K * |y|))
    (Metric.ball_mem_nhds s₀ (by linarith : 0 < s₀ / 2)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall (fun s => (hfc.comp (by fun_prop)).aestronglyMeasurable)
  · exact integrable_bdd_comp f hfc.measurable C hfb _ _
  · exact ((hdfc.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall (fun y s hs => ?_)
    obtain ⟨_, ha, hb⟩ := hball s hs
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |-Real.exp (-s) * x + Real.exp (-(2 * s)) / ouB s * y| ≤ |x| + K * |y| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_neg]
      have := mul_le_mul_of_nonneg_right ha (abs_nonneg x)
      have := mul_le_mul_of_nonneg_right hb (abs_nonneg y)
      linarith
    exact mul_le_mul (hdf _) h1 (abs_nonneg _) hC
  · exact (integrable_const _ |>.add (integrable_abs_y.const_mul K)).const_mul C
  · refine Eventually.of_forall (fun y s hs => ?_)
    exact hasDerivAt_integrand_time f hfd x y s (hball s hs).1

lemma abs_ouP_le (k : ℝ → ℝ) (hk : Measurable k) (B : ℝ) (hB : ∀ z, |k z| ≤ B) (s x : ℝ) :
    |ouP s k x| ≤ B := by
  unfold ouP
  refine (abs_integral_le_integral_abs).trans ?_
  have := integral_mono (integrable_bdd_comp k hk B hB (Real.exp (-s) * x) (ouB s)).abs
    (integrable_const B) (fun y => hB _)
  simpa using this

lemma abs_noise_moment_le (k : ℝ → ℝ) (hk : Measurable k) (B : ℝ) (hB : ∀ z, |k z| ≤ B)
    (c d : ℝ) :
    |∫ y, y * k (c + d * y) ∂(gaussianReal 0 1)| ≤ B * ∫ y, |y| ∂(gaussianReal 0 1) := by
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono (integrable_y_mul_bdd_comp k hk B hB c d).abs
    (integrable_abs_y.const_mul B) (fun y => ?_)
  simp only [abs_mul]
  rw [mul_comm B]
  exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)

/-! ### Spatial derivatives at a fixed time `t > 0` -/

section Spatial

variable (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ) (hfb : ∀ z, |f z| ≤ C)
  (hdf : ∀ z, |deriv f z| ≤ C) (t : ℝ) (ht : 0 < t)
include hf hfb hdf ht

/-- Gaussian integration by parts in the noise variable:
`b ∫ f'(a x + b y) dγ(y) = ∫ y f(a x + b y) dγ(y)`. -/
lemma ibp_noise (x : ℝ) :
    ouB t * ouP t (deriv f) x
      = ∫ y, y * f (Real.exp (-t) * x + ouB t * y) ∂(gaussianReal 0 1) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hder : ∀ y, HasDerivAt (fun y => f (Real.exp (-t) * x + ouB t * y))
      (deriv f (Real.exp (-t) * x + ouB t * y) * ouB t) y := by
    intro y
    have h1 : HasDerivAt (fun y => Real.exp (-t) * x + ouB t * y) (ouB t) y := by
      simpa using ((hasDerivAt_id y).const_mul (ouB t)).const_add (Real.exp (-t) * x)
    exact (hfd _).hasDerivAt.comp y h1
  have := gaussian_ibp_one_dim (fun y => f (Real.exp (-t) * x + ouB t * y))
    (fun y => (hder y).differentiableAt) (C * |ouB t|) (fun y => by
      rw [(hder y).deriv, abs_mul]
      exact mul_le_mul_of_nonneg_right (hdf _) (abs_nonneg _))
  rw [this]
  simp_rw [fun y => (hder y).deriv]
  rw [integral_mul_const, mul_comm]
  rfl

lemma hasDerivAt_noise_moment (x : ℝ) :
    HasDerivAt (fun z => ∫ y, y * f (Real.exp (-t) * z + ouB t * y) ∂(gaussianReal 0 1))
      (Real.exp (-t) * ∫ y, y * deriv f (Real.exp (-t) * x + ouB t * y) ∂(gaussianReal 0 1)) x := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  rw [← integral_const_mul]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun z y => y * f (Real.exp (-t) * z + ouB t * y))
    (F' := fun z y => Real.exp (-t) * (y * deriv f (Real.exp (-t) * z + ouB t * y)))
    (x₀ := x) (bound := fun y => Real.exp (-t) * (C * |y|)) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall (fun z => (continuous_id.mul
      (hfc.comp (by fun_prop))).aestronglyMeasurable)
  · exact integrable_y_mul_bdd_comp f hfc.measurable C hfb _ _
  · exact ((continuous_id.mul (hdfc.comp (by fun_prop))).const_mul _).aestronglyMeasurable
  · refine Eventually.of_forall (fun y z _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm C]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdf _) (abs_nonneg _))
      (Real.exp_pos _).le
  · exact (integrable_abs_y.const_mul C).const_mul _
  · refine Eventually.of_forall (fun y z _ => ?_)
    have h1 : HasDerivAt (fun z => Real.exp (-t) * z + ouB t * y) (Real.exp (-t)) z := by
      simpa using ((hasDerivAt_id z).const_mul (Real.exp (-t))).add_const (ouB t * y)
    have := ((hfd _).hasDerivAt.comp z h1).const_mul y
    refine this.congr_deriv ?_
    ring

/-- First spatial derivative: `(P_t f)' = e^{-t} P_t f'` (from the commutation child). -/
lemma hasDerivAt_ouP_space (x : ℝ) :
    HasDerivAt (ouP t f) (Real.exp (-t) * ouP t (deriv f) x) x :=
  ou_semigroup_commutation f hf C hdf t x

lemma deriv_ouP_eq :
    deriv (ouP t f) = fun x => Real.exp (-t) / ouB t
      * ∫ y, y * f (Real.exp (-t) * x + ouB t * y) ∂(gaussianReal 0 1) := by
  funext x
  rw [(hasDerivAt_ouP_space f hf C hfb hdf t ht x).deriv,
    ← ibp_noise f hf C hfb hdf t ht x]
  have := ouB_pos ht
  field_simp

/-- Second spatial derivative of `P_t f` for `t > 0`, computed with only `f ∈ C¹`. -/
lemma hasDerivAt_deriv_ouP (x : ℝ) :
    HasDerivAt (deriv (ouP t f))
      (Real.exp (-t) ^ 2 / ouB t
        * ∫ y, y * deriv f (Real.exp (-t) * x + ouB t * y) ∂(gaussianReal 0 1)) x := by
  rw [deriv_ouP_eq f hf C hfb hdf t ht]
  have := (hasDerivAt_noise_moment f hf C hfb hdf t ht x).const_mul (Real.exp (-t) / ouB t)
  refine this.congr_deriv ?_
  ring

/-- The generator identity `∂ₜ P_t f = (P_t f)'' - x (P_t f)'`. -/
lemma time_deriv_eq_generator (x : ℝ) :
    ∫ y, deriv f (Real.exp (-t) * x + ouB t * y)
        * (-Real.exp (-t) * x + Real.exp (-(2 * t)) / ouB t * y) ∂(gaussianReal 0 1)
      = deriv (deriv (ouP t f)) x - x * deriv (ouP t f) x := by
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  rw [(hasDerivAt_deriv_ouP f hf C hfb hdf t ht x).deriv,
    (hasDerivAt_ouP_space f hf C hfb hdf t ht x).deriv]
  have e : ∀ y, deriv f (Real.exp (-t) * x + ouB t * y)
      * (-Real.exp (-t) * x + Real.exp (-(2 * t)) / ouB t * y)
      = (-Real.exp (-t) * x) * deriv f (Real.exp (-t) * x + ouB t * y)
        + Real.exp (-(2 * t)) / ouB t * (y * deriv f (Real.exp (-t) * x + ouB t * y)) := by
    intro y; ring
  simp_rw [e]
  have i1 : Integrable (fun y => (-Real.exp (-t) * x) * deriv f (Real.exp (-t) * x + ouB t * y))
      (gaussianReal 0 1) :=
    (integrable_bdd_comp (deriv f) hdfc.measurable C hdf _ _).const_mul _
  have i2 : Integrable (fun y => Real.exp (-(2 * t)) / ouB t
      * (y * deriv f (Real.exp (-t) * x + ouB t * y))) (gaussianReal 0 1) :=
    (integrable_y_mul_bdd_comp (deriv f) hdfc.measurable C hdf _ _).const_mul _
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul, ouB_sq_eq_exp]
  unfold ouP
  ring

lemma abs_deriv_ouP_le (x : ℝ) : |deriv (ouP t f) x| ≤ C := by
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  rw [(hasDerivAt_ouP_space f hf C hfb hdf t ht x).deriv, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have h1 := abs_ouP_le (deriv f) hdfc.measurable C hdf t x
  have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hdf 0)
  nlinarith [Real.exp_pos (-t), abs_nonneg (ouP t (deriv f) x)]

lemma abs_deriv_deriv_ouP_le (x : ℝ) :
    |deriv (deriv (ouP t f)) x| ≤ 1 / ouB t * (C * ∫ y, |y| ∂(gaussianReal 0 1)) := by
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  rw [(hasDerivAt_deriv_ouP f hf C hfb hdf t ht x).deriv, abs_mul]
  have hb := ouB_pos ht
  have h1 := abs_noise_moment_le (deriv f) hdfc.measurable C hdf (Real.exp (-t) * x) (ouB t)
  have h2 : |Real.exp (-t) ^ 2 / ouB t| ≤ 1 / ouB t := by
    rw [abs_of_pos (by positivity)]
    apply div_le_div_of_nonneg_right _ hb.le
    rw [ouB_sq_eq_exp]; exact Real.exp_le_one_iff.2 (by linarith)
  exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)

/-- Integration by parts in the space variable (Gaussian `x`): for `u = P_t f`,
`∫ (log u + 1) (u'' - x u') dγ = -∫ u'²/u dγ`. -/
lemma entropy_ibp_space (δ : ℝ) (hδ : 0 < δ) (hlow : ∀ z, δ ≤ f z) :
    ∫ x, (Real.log (ouP t f x) + 1)
        * (deriv (deriv (ouP t f)) x - x * deriv (ouP t f) x) ∂(gaussianReal 0 1)
      = -∫ x, deriv (ouP t f) x ^ 2 / ouP t f x ∂(gaussianReal 0 1) := by
  have hfc : Continuous f := hf.continuous
  set u := ouP t f with hu
  have hC : 0 ≤ C := (abs_nonneg _).trans (hdf 0)
  have hδC : δ ≤ C := (hlow 0).trans ((le_abs_self _).trans (hfb 0))
  have hu_low : ∀ x, δ ≤ u x := by
    intro x
    have := integral_mono (integrable_const δ) (integrable_bdd_comp f hfc.measurable C hfb
      (Real.exp (-t) * x) (ouB t)) (fun y => hlow _)
    simpa [hu, ouP] using this
  have hu_up : ∀ x, u x ≤ C := fun x =>
    (le_abs_self _).trans (abs_ouP_le f hfc.measurable C hfb t x)
  have hu_pos : ∀ x, 0 < u x := fun x => lt_of_lt_of_le hδ (hu_low x)
  set K1 := |Real.log δ| + |Real.log C| + 1 with hK1
  have hlog : ∀ x, |Real.log (u x) + 1| ≤ K1 := by
    intro x
    have h1 : Real.log δ ≤ Real.log (u x) := Real.log_le_log hδ (hu_low x)
    have h2 : Real.log (u x) ≤ Real.log C := Real.log_le_log (hu_pos x) (hu_up x)
    refine (abs_add_le _ _).trans ?_
    rw [abs_one]
    have : |Real.log (u x)| ≤ |Real.log δ| + |Real.log C| := by
      rw [abs_le]; constructor
      · linarith [neg_abs_le (Real.log δ), abs_nonneg (Real.log C)]
      · linarith [le_abs_self (Real.log C), abs_nonneg (Real.log δ)]
    linarith
  set B2 := 1 / ouB t * (C * ∫ y, |y| ∂(gaussianReal 0 1)) with hB2
  have hB2 : 0 ≤ B2 := by
    have := ouB_pos ht
    have : 0 ≤ ∫ y, |y| ∂(gaussianReal 0 1) := integral_nonneg (fun y => abs_nonneg y)
    positivity
  have hd1 : ∀ x, HasDerivAt u (deriv u x) x := fun x =>
    (hasDerivAt_ouP_space f hf C hfb hdf t ht x).differentiableAt.hasDerivAt
  have hd2 : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x =>
    (hasDerivAt_deriv_ouP f hf C hfb hdf t ht x).differentiableAt.hasDerivAt
  have hucont : Continuous u := continuous_iff_continuousAt.2 (fun x => (hd1 x).continuousAt)
  have hb1 : ∀ x, |deriv u x| ≤ C := abs_deriv_ouP_le f hf C hfb hdf t ht
  have hb2 : ∀ x, |deriv (deriv u) x| ≤ B2 := abs_deriv_deriv_ouP_le f hf C hfb hdf t ht
  -- the function `h = u' (log u + 1)`
  set h : ℝ → ℝ := fun x => deriv u x * (Real.log (u x) + 1) with hh
  have hdh : ∀ x, HasDerivAt h
      (deriv (deriv u) x * (Real.log (u x) + 1) + deriv u x * (deriv u x / u x)) x := by
    intro x
    have hl := ((hd1 x).log (hu_pos x).ne').add_const 1
    exact (hd2 x).mul hl
  have hdh_bound : ∀ x, |deriv h x| ≤ B2 * K1 + C * (C / δ) := by
    intro x
    rw [(hdh x).deriv]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_div, abs_of_pos (hu_pos x)]
    have e1 := mul_le_mul (hb2 x) (hlog x) (abs_nonneg _) hB2
    have e2 : |deriv u x| / u x ≤ C / δ := by
      rw [div_le_div_iff₀ (hu_pos x) hδ]
      nlinarith [hb1 x, hu_low x, abs_nonneg (deriv u x)]
    have e3 := mul_le_mul (hb1 x) e2 (div_nonneg (abs_nonneg _) (hu_pos x).le) hC
    linarith
  have hibp := gaussian_ibp_one_dim h (fun x => (hdh x).differentiableAt) _ hdh_bound
  simp_rw [fun x => (hdh x).deriv] at hibp
  -- integrability
  have hm1 : Measurable (deriv u) := measurable_deriv u
  have hm2 : Measurable (deriv (deriv u)) := measurable_deriv _
  have hmlog : Measurable (fun x => Real.log (u x) + 1) :=
    (hucont.measurable.log).add_const 1
  have iA : Integrable (fun x => deriv (deriv u) x * (Real.log (u x) + 1)) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const (B2 * K1)) (hm2.mul hmlog).aestronglyMeasurable
      (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hb2 x) (hlog x) (abs_nonneg _) hB2
  have iB : Integrable (fun x => deriv u x * (deriv u x / u x)) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const (C * (C / δ)))
      (hm1.mul (hm1.div hucont.measurable)).aestronglyMeasurable
      (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (hu_pos x)]
    have e2 : |deriv u x| / u x ≤ C / δ := by
      rw [div_le_div_iff₀ (hu_pos x) hδ]
      nlinarith [hb1 x, hu_low x, abs_nonneg (deriv u x)]
    exact mul_le_mul (hb1 x) e2 (div_nonneg (abs_nonneg _) (hu_pos x).le) hC
  have iX : Integrable (fun x => x * h x) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_abs_y.const_mul (C * K1))
      ((measurable_id.mul (hm1.mul hmlog))).aestronglyMeasurable
      (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul, hh]
    simp only [abs_mul]
    rw [mul_comm (C * K1)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hb1 x) (hlog x) (abs_nonneg _) hC)
      (abs_nonneg _)
  have e : ∀ x, (Real.log (u x) + 1) * (deriv (deriv u) x - x * deriv u x)
      = deriv (deriv u) x * (Real.log (u x) + 1) - x * h x := by
    intro x; simp only [hh]; ring
  simp_rw [e]
  rw [integral_sub iA iX, hibp, integral_add iA iB]
  have e2 : ∀ x, deriv u x * (deriv u x / u x) = deriv u x ^ 2 / u x := by
    intro x; ring
  simp_rw [e2]
  ring

end Spatial

end GaussianMatrix

namespace GaussianMatrix

open Filter Topology Set

lemma ouB_ball_bounds {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs : s ∈ Metric.ball s₀ (s₀ / 2)) :
    0 < s ∧ |Real.exp (-s)| ≤ 1 ∧ |Real.exp (-(2 * s)) / ouB s| ≤ 1 / ouB (s₀ / 2) := by
  have hb0 : 0 < ouB (s₀ / 2) := ouB_pos (by linarith)
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  have hs1 : s₀ / 2 < s := by linarith
  have hspos : 0 < s := by linarith
  refine ⟨hspos, ?_, ?_⟩
  · rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.2 (by linarith)
  · have hbs : ouB (s₀ / 2) ≤ ouB s := ouB_mono hs1.le
    rw [abs_of_pos (div_pos (Real.exp_pos _) (ouB_pos hspos)),
      div_le_div_iff₀ (ouB_pos hspos) hb0]
    have : Real.exp (-(2 * s)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith

end GaussianMatrix

open GaussianMatrix Filter Topology Set

theorem GaussianMatrix.ou_entropy_hasDerivAt (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (δ C : ℝ) (hδ : 0 < δ)
    (hlow : ∀ x, δ ≤ f x) (hup : ∀ x, f x ≤ C) (hdf : ∀ x, |deriv f x| ≤ C) (t : ℝ)
    (ht : 0 < t) :
    HasDerivAt
      (fun s => ∫ x,
        (∫ y, f (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-(2 * s))) * y) ∂(gaussianReal 0 1))
          * Real.log (∫ y, f (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-(2 * s))) * y)
              ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1))
      (-∫ x,
        deriv (fun z => ∫ y, f (Real.exp (-t) * z + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
            ∂(gaussianReal 0 1)) x ^ 2
          / ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y) ∂(gaussianReal 0 1)
        ∂(gaussianReal 0 1)) t := by
  show HasDerivAt (fun s => ∫ x, ouP s f x * Real.log (ouP s f x) ∂(gaussianReal 0 1))
    (-∫ x, deriv (ouP t f) x ^ 2 / ouP t f x ∂(gaussianReal 0 1)) t
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hC : δ ≤ C := (hlow 0).trans (hup 0)
  have hC0 : 0 < C := lt_of_lt_of_le hδ hC
  have hfb : ∀ x, |f x| ≤ C := fun x => by
    rw [abs_of_pos (lt_of_lt_of_le hδ (hlow x))]; exact hup x
  -- bounds on the semigroup, uniformly in time
  have hu_low : ∀ s x, δ ≤ ouP s f x := by
    intro s x
    have := integral_mono (integrable_const δ) (integrable_bdd_comp f hfc.measurable C hfb
      (Real.exp (-s) * x) (ouB s)) (fun y => hlow _)
    simpa [ouP] using this
  have hu_up : ∀ s x, ouP s f x ≤ C := fun s x =>
    (le_abs_self _).trans (abs_ouP_le f hfc.measurable C hfb s x)
  have hu_pos : ∀ s x, 0 < ouP s f x := fun s x => lt_of_lt_of_le hδ (hu_low s x)
  set K1 := |Real.log δ| + |Real.log C| + 1 with hK1
  have hlog : ∀ s x, |Real.log (ouP s f x)| ≤ K1 - 1 := by
    intro s x
    have h1 : Real.log δ ≤ Real.log (ouP s f x) := Real.log_le_log hδ (hu_low s x)
    have h2 : Real.log (ouP s f x) ≤ Real.log C := Real.log_le_log (hu_pos s x) (hu_up s x)
    rw [abs_le]; constructor
    · linarith [neg_abs_le (Real.log δ), abs_nonneg (Real.log C)]
    · linarith [le_abs_self (Real.log C), abs_nonneg (Real.log δ)]
  have hlog1 : ∀ s x, |Real.log (ouP s f x) + 1| ≤ K1 := fun s x => by
    refine (abs_add_le _ _).trans ?_; rw [abs_one]; linarith [hlog s x]
  have hK1 : 0 ≤ K1 := (abs_nonneg _).trans (hlog1 0 0)
  have hcont : ∀ s, Continuous (ouP s f) := fun s => continuous_iff_continuousAt.2
    (fun x => (ou_semigroup_commutation f hf C hdf s x :
      HasDerivAt (ouP s f) _ x).continuousAt)
  -- the time derivative `D s x` of `P_s f(x)` and its bound
  set D : ℝ → ℝ → ℝ := fun s x => ∫ y, deriv f (Real.exp (-s) * x + ouB s * y)
        * (-Real.exp (-s) * x + Real.exp (-(2 * s)) / ouB s * y) ∂(gaussianReal 0 1) with hD
  set K := 1 / ouB (t / 2) with hK
  set M1 := ∫ y, |y| ∂(gaussianReal 0 1) with hM1
  have hD_bound : ∀ s ∈ Metric.ball t (t / 2), ∀ x, |D s x| ≤ C * |x| + C * K * M1 := by
    intro s hs x
    obtain ⟨_, ha, hb⟩ := ouB_ball_bounds ht hs
    have hint : Integrable (fun y : ℝ => C * (|x| + K * |y|)) (gaussianReal 0 1) :=
      ((integrable_const _).add (integrable_abs_y.const_mul K)).const_mul C
    have := norm_integral_le_of_norm_le (f := fun y => deriv f (Real.exp (-s) * x + ouB s * y)
        * (-Real.exp (-s) * x + Real.exp (-(2 * s)) / ouB s * y)) hint
      (Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |-Real.exp (-s) * x + Real.exp (-(2 * s)) / ouB s * y| ≤ |x| + K * |y| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_neg]
        have := mul_le_mul_of_nonneg_right ha (abs_nonneg x)
        have := mul_le_mul_of_nonneg_right hb (abs_nonneg y)
        linarith
      exact mul_le_mul (hdf _) h1 (abs_nonneg _) hC0.le))
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (integrable_const _) (integrable_abs_y.const_mul K),
      integral_const_mul]
    simp; ring
  -- differentiate under the integral sign in `x`
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun s x => ouP s f x * Real.log (ouP s f x))
    (F' := fun s x => (Real.log (ouP s f x) + 1) * D s x)
    (x₀ := t) (bound := fun x => K1 * (C * |x| + C * K * M1))
    (Metric.ball_mem_nhds t (by linarith : 0 < t / 2)) ?_ ?_ ?_ ?_ ?_ ?_
  · refine hmain.2.congr_deriv ?_
    have e : ∀ x, (Real.log (ouP t f x) + 1) * D t x = (Real.log (ouP t f x) + 1)
        * (deriv (deriv (ouP t f)) x - x * deriv (ouP t f) x) := by
      intro x
      rw [hD]
      simp only
      rw [time_deriv_eq_generator f hf C hfb hdf t ht x]
    simp_rw [e]
    exact entropy_ibp_space f hf C hfb hdf t ht δ hδ hlow
  · exact Eventually.of_forall (fun s =>
      ((hcont s).measurable.mul (hcont s).measurable.log).aestronglyMeasurable)
  · refine Integrable.mono' (integrable_const (C * (K1 - 1)))
      ((hcont t).measurable.mul (hcont t).measurable.log).aestronglyMeasurable
      (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((le_abs_self _).trans (abs_ouP_le f hfc.measurable C hfb t x) |>.trans'
      (by rw [abs_of_pos (hu_pos t x)])) (hlog t x) (abs_nonneg _) hC0.le
  · have e : D t = fun x => deriv (deriv (ouP t f)) x - x * deriv (ouP t f) x :=
      funext (time_deriv_eq_generator f hf C hfb hdf t ht)
    rw [show (fun x => (Real.log (ouP t f x) + 1) * D t x)
      = fun x => (Real.log (ouP t f x) + 1) * (deriv (deriv (ouP t f)) x
          - x * deriv (ouP t f) x) from by rw [e]]
    exact (((hcont t).measurable.log.add_const 1).mul ((measurable_deriv _).sub
      (measurable_id.mul (measurable_deriv _)))).aestronglyMeasurable
  · refine Eventually.of_forall (fun x s hs => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hlog1 s x) (hD_bound s hs x) (abs_nonneg _) hK1
  · exact (((integrable_abs_y.const_mul C).add (integrable_const _))).const_mul K1
  · refine Eventually.of_forall (fun x s hs => ?_)
    have h1 := hasDerivAt_ouP_time f hf C hfb hdf x s (ouB_ball_bounds ht hs).1
    exact (Real.hasDerivAt_mul_log (hu_pos s x).ne').comp s h1

/-! ## `gaussian_logsobolev_bounded_below` -/

namespace GaussianMatrix

open Filter Topology Set

/-- The one-dimensional Ornstein–Uhlenbeck semigroup (Mehler formula). -/
noncomputable def ouSG (t : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, h (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y) ∂(gaussianReal 0 1)

/-- `|s log s| ≤ s² + 1` for `s ≥ 0`. -/
lemma abs_mul_log_le_sq_add_one' (s : ℝ) (hs : 0 ≤ s) : |s * Real.log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with h | hs'
  · subst h; simp
  rcases le_or_gt s 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt s hs' h1
    rw [mul_comm]; nlinarith [sq_nonneg s]
  · have hl : 0 ≤ Real.log s := Real.log_nonneg h1.le
    have hl2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs'
    rw [abs_of_nonneg (mul_nonneg hs hl)]
    nlinarith

/-- Cauchy–Schwarz in the form `(∫ a)² ≤ (∫ a²/b) (∫ b)` for `b ≥ δ > 0`. -/
lemma sq_integral_le_integral_div_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (a b : α → ℝ) (δ : ℝ) (hδ : 0 < δ) (hb : ∀ x, δ ≤ b x)
    (ha : Integrable a μ) (hbi : Integrable b μ) (hab : Integrable (fun x => a x ^ 2 / b x) μ) :
    (∫ x, a x ∂μ) ^ 2 ≤ (∫ x, a x ^ 2 / b x ∂μ) * (∫ x, b x ∂μ) := by
  set A := ∫ x, a x ∂μ
  set B := ∫ x, b x ∂μ
  set Q := ∫ x, a x ^ 2 / b x ∂μ
  have hB : δ ≤ B := by
    have := integral_mono (integrable_const δ) hbi hb
    simpa using this
  have hBpos : 0 < B := lt_of_lt_of_le hδ hB
  set l := A / B
  have hpt : ∀ x, (a x - l * b x) ^ 2 / b x = a x ^ 2 / b x - 2 * l * a x + l ^ 2 * b x := by
    intro x
    have : b x ≠ 0 := (lt_of_lt_of_le hδ (hb x)).ne'
    field_simp
    ring
  have hnonneg : 0 ≤ ∫ x, (a x - l * b x) ^ 2 / b x ∂μ := by
    refine integral_nonneg (fun x => div_nonneg (sq_nonneg _) (hδ.le.trans (hb x)))
  have hcalc : ∫ x, (a x - l * b x) ^ 2 / b x ∂μ = Q - 2 * l * A + l ^ 2 * B := by
    simp_rw [hpt]
    have h1 : Integrable (fun x => a x ^ 2 / b x - 2 * l * a x) μ := hab.sub (ha.const_mul _)
    have h2 : Integrable (fun x => l ^ 2 * b x) μ := hbi.const_mul _
    have h3 : Integrable (fun x => 2 * l * a x) μ := ha.const_mul _
    rw [integral_add h1 h2, integral_sub hab h3, integral_const_mul, integral_const_mul]
  rw [hcalc] at hnonneg
  have : Q - 2 * l * A + l ^ 2 * B = Q - A ^ 2 / B := by
    simp only [l]; field_simp; ring
  rw [this, sub_nonneg, div_le_iff₀ hBpos] at hnonneg
  exact hnonneg

end GaussianMatrix

open GaussianMatrix Filter Topology Set

theorem GaussianMatrix.gaussian_logsobolev_bounded_below (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (δ C : ℝ)
    (hδ : 0 < δ) (hlow : ∀ x, δ ≤ f x) (hup : ∀ x, f x ≤ C) (hdf : ∀ x, |deriv f x| ≤ C) :
    ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1)
      - (∫ x, f x ∂(gaussianReal 0 1)) * Real.log (∫ x, f x ∂(gaussianReal 0 1))
      ≤ (1 / 2) * ∫ x, deriv f x ^ 2 / f x ∂(gaussianReal 0 1) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hC : δ ≤ C := (hlow 0).trans (hup 0)
  have hC0 : 0 < C := lt_of_lt_of_le hδ hC
  have hfabs : ∀ x, |f x| ≤ C := fun x => by
    rw [abs_of_pos (lt_of_lt_of_le hδ (hlow x))]; exact hup x
  -- integrability of bounded continuous functions composed with affine maps
  have hint_aff : ∀ (h : ℝ → ℝ), Measurable h → (∀ z, |h z| ≤ C ^ 2 / δ + C) →
      ∀ a b : ℝ, Integrable (fun y => h (a + b * y)) (gaussianReal 0 1) := by
    intro h hm hb a b
    refine Integrable.mono' (integrable_const (C ^ 2 / δ + C))
      (hm.comp (by fun_prop)).aestronglyMeasurable (Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs]; exact hb _
  have hδC : 0 ≤ C ^ 2 / δ := by positivity
  have hf_int : ∀ a b : ℝ, Integrable (fun y => f (a + b * y)) (gaussianReal 0 1) :=
    hint_aff f hfc.measurable (fun z => by linarith [hfabs z])
  -- basic bounds on the semigroup
  have hP_low : ∀ t x, δ ≤ ouSG t f x := by
    intro t x
    have := integral_mono (integrable_const δ)
      (hf_int (Real.exp (-t) * x) (Real.sqrt (1 - Real.exp (-(2 * t))))) (fun y => hlow _)
    simpa [ouSG] using this
  have hP_up : ∀ t x, ouSG t f x ≤ C := by
    intro t x
    have := integral_mono (hf_int (Real.exp (-t) * x) (Real.sqrt (1 - Real.exp (-(2 * t)))))
      (integrable_const C) (fun y => hup _)
    simpa [ouSG] using this
  have hP_pos : ∀ t x, 0 < ouSG t f x := fun t x => lt_of_lt_of_le hδ (hP_low t x)
  have hP0 : ∀ x, ouSG 0 f x = f x := by intro x; simp [ouSG]
  -- differentiability (hence continuity, measurability) in `x`
  have hP_hasDeriv : ∀ t x, HasDerivAt (ouSG t f) (Real.exp (-t) * ouSG t (deriv f) x) x :=
    fun t x => ou_semigroup_commutation f hf C hdf t x
  have hP_cont : ∀ t, Continuous (ouSG t f) := fun t =>
    continuous_iff_continuousAt.2 (fun x => (hP_hasDeriv t x).continuousAt)
  -- continuity in `t`
  have hP_cont_t : ∀ x, Continuous (fun t => ouSG t f x) := by
    intro x
    refine continuous_of_dominated (bound := fun _ => C) (fun t => ?_)
      (fun t => Eventually.of_forall (fun y => ?_)) (integrable_const C)
      (Eventually.of_forall (fun y => ?_))
    · exact (hfc.comp (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hfabs _
    · exact hfc.comp (by fun_prop)
  -- the entropy functional along the semigroup
  set H : ℝ → ℝ := fun t => ∫ x, ouSG t f x * Real.log (ouSG t f x) ∂(gaussianReal 0 1)
    with hHdef
  have hΦbound : ∀ t x, |ouSG t f x * Real.log (ouSG t f x)| ≤ C ^ 2 + 1 := by
    intro t x
    refine (abs_mul_log_le_sq_add_one' _ (hP_pos t x).le).trans ?_
    have := pow_le_pow_left₀ (hP_pos t x).le (hP_up t x) 2
    linarith
  have hH_cont : Continuous H := by
    refine continuous_of_dominated (bound := fun _ => C ^ 2 + 1) (fun t => ?_)
      (fun t => Eventually.of_forall (fun x => ?_)) (integrable_const _)
      (Eventually.of_forall (fun x => ?_))
    · exact ((hP_cont t).measurable.mul (hP_cont t).measurable.log).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hΦbound t x
    · exact Real.continuous_mul_log.comp (hP_cont_t x)
  -- Fisher information and its decay
  set J := ∫ x, deriv f x ^ 2 / f x ∂(gaussianReal 0 1) with hJdef
  set I : ℝ → ℝ := fun t =>
    ∫ x, deriv (ouSG t f) x ^ 2 / ouSG t f x ∂(gaussianReal 0 1) with hIdef
  have hH_deriv : ∀ t, 0 < t → HasDerivAt H (-I t) t := fun t ht =>
    ou_entropy_hasDerivAt f hf δ C hδ hlow hup hdf t ht
  set q : ℝ → ℝ := fun z => deriv f z ^ 2 / f z with hqdef
  have hq_meas : Measurable q := ((measurable_deriv f).pow_const 2).div hfc.measurable
  have hq_bound : ∀ z, |q z| ≤ C ^ 2 / δ + C := by
    intro z
    have hfz := lt_of_lt_of_le hδ (hlow z)
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hfz.le)]
    have h1 : deriv f z ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdf z) 2
    have h2 : deriv f z ^ 2 / f z ≤ C ^ 2 / δ := by
      rw [div_le_div_iff₀ hfz hδ]
      nlinarith [hlow z, sq_nonneg (deriv f z)]
    linarith
  have hq_int : Integrable q (gaussianReal 0 1) := by
    simpa using hint_aff q hq_meas hq_bound 0 1
  have hI_le : ∀ t, 0 ≤ t → I t ≤ Real.exp (-(2 * t)) * J := by
    intro t ht
    have hinv : ∫ x, ouSG t q x ∂(gaussianReal 0 1) = J :=
      ou_semigroup_invariant q hq_int t ht
    -- pointwise Cauchy–Schwarz
    have hpt : ∀ x, deriv (ouSG t f) x ^ 2 / ouSG t f x
        ≤ Real.exp (-(2 * t)) * ouSG t q x := by
      intro x
      rw [(hP_hasDeriv t x).deriv]
      have hCS := sq_integral_le_integral_div_mul (gaussianReal 0 1)
        (fun y => deriv f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y))
        (fun y => f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)) δ hδ
        (fun y => hlow _)
        (hint_aff (deriv f) (measurable_deriv f) (fun z => by
          linarith [hdf z, show C ≤ C ^ 2 / δ + C by linarith]) _ _)
        (hf_int _ _) (hint_aff q hq_meas hq_bound _ _)
      have hP := hP_pos t x
      rw [div_le_iff₀ hP, mul_pow, ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * -t = -(2 * t) := by push_cast; ring
      rw [e, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact hCS
    have hmeas_q : Integrable (ouSG t q) (gaussianReal 0 1) := by
      refine Integrable.mono' (integrable_const (C ^ 2 / δ + C)) ?_
        (Eventually.of_forall (fun x => ?_))
      · refine (StronglyMeasurable.integral_prod_right'
          (f := fun p : ℝ × ℝ => q (Real.exp (-t) * p.1
            + Real.sqrt (1 - Real.exp (-(2 * t))) * p.2)) ?_).aestronglyMeasurable
        exact (hq_meas.comp (by fun_prop)).stronglyMeasurable
      · rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        have := integral_mono (hint_aff q hq_meas hq_bound (Real.exp (-t) * x)
          (Real.sqrt (1 - Real.exp (-(2 * t))))).abs
          (integrable_const (C ^ 2 / δ + C)) (fun y => hq_bound _)
        simpa using this
    calc I t ≤ ∫ x, Real.exp (-(2 * t)) * ouSG t q x ∂(gaussianReal 0 1) := by
          refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_))
            (hmeas_q.const_mul _) (Eventually.of_forall hpt)
          exact div_nonneg (sq_nonneg _) (hP_pos t x).le
      _ = Real.exp (-(2 * t)) * J := by rw [integral_const_mul, hinv]
  -- monotonicity of `Ψ(t) = H(t) - e^{-2t} J / 2` on `[0, ∞)`
  set Ψ : ℝ → ℝ := fun t => H t - (1 / 2) * Real.exp (-(2 * t)) * J with hΨdef
  have hΨ_mono : MonotoneOn Ψ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => -I t + Real.exp (-(2 * t)) * J)
      (convex_Ici 0) (by fun_prop) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Ici] at ht
      have h1 := hH_deriv t ht
      have h2 : HasDerivAt (fun t : ℝ => (1 / 2) * Real.exp (-(2 * t)) * J)
          (-(Real.exp (-(2 * t)) * J)) t := by
        have := (((hasDerivAt_id t).const_mul 2).neg.exp.const_mul (1 / 2)).mul_const J
        refine this.congr_deriv ?_
        simp only [Pi.neg_apply, id]; ring
      exact (h1.sub h2).hasDerivWithinAt.congr_deriv (by ring)
    · rw [interior_Ici] at ht
      have := hI_le t (le_of_lt ht)
      linarith
  -- behaviour at infinity
  set m := ∫ x, f x ∂(gaussianReal 0 1) with hmdef
  have hP_lim : ∀ x, Tendsto (fun t => ouSG t f x) atTop (𝓝 m) := by
    intro x
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      (Eventually.of_forall (fun t => (hfc.comp (by fun_prop)).aestronglyMeasurable))
      (Eventually.of_forall (fun t => Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact hfabs _))) (integrable_const C)
      (Eventually.of_forall (fun y => ?_))
    have h1 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have h3 : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-(2 * t)))) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h2).sqrt
      simpa using this
    have h4 : Tendsto (fun t : ℝ => Real.exp (-t) * x
        + Real.sqrt (1 - Real.exp (-(2 * t))) * y) atTop (𝓝 y) := by
      have := (h1.mul_const x).add (h3.mul_const y)
      simpa using this
    exact (hfc.tendsto y).comp h4
  have hH_lim : Tendsto H atTop (𝓝 (m * Real.log m)) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1)
      (F := fun t x => ouSG t f x * Real.log (ouSG t f x)) (f := fun _ => m * Real.log m)
      (l := atTop) (fun _ => C ^ 2 + 1)
      (Eventually.of_forall (fun t =>
        ((hP_cont t).measurable.mul (hP_cont t).measurable.log).aestronglyMeasurable))
      (Eventually.of_forall (fun t => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]; exact hΦbound t x))) (integrable_const _)
      (Eventually.of_forall (fun x => (Real.continuous_mul_log.tendsto _).comp (hP_lim x)))
    simpa using this
  have hΨ_lim : Tendsto Ψ atTop (𝓝 (m * Real.log m)) := by
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have := hH_lim.sub ((h2.const_mul (1 / 2)).mul_const J)
    simpa [Ψ, mul_assoc] using this
  have hΨ0 : Ψ 0 ≤ m * Real.log m := by
    refine ge_of_tendsto hΨ_lim ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hΨ_mono (self_mem_Ici) ht ht
  have hH0 : H 0 = ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1) := by
    simp only [H, hP0]
  have : Ψ 0 = ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1) - (1 / 2) * J := by
    simp only [Ψ, hH0]; simp
  rw [this] at hΨ0
  linarith

/-! ## `gaussian_logsobolev_one_dim_compact_support` -/

namespace GaussianMatrix

open Filter Topology

/-- `|s log s| ≤ s² + 1` for `s ≥ 0`. -/
lemma abs_mul_log_le_sq_add_one (s : ℝ) (hs : 0 ≤ s) : |s * Real.log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with h | hs'
  · subst h; simp
  rcases le_or_gt s 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt s hs' h1
    rw [mul_comm]; nlinarith [sq_nonneg s]
  · have hl : 0 ≤ Real.log s := Real.log_nonneg h1.le
    have hl2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs'
    rw [abs_of_nonneg (mul_nonneg hs hl)]
    nlinarith

end GaussianMatrix

open GaussianMatrix Filter Topology

theorem GaussianMatrix.gaussian_logsobolev_one_dim_compact_support (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    ∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1)
      - (∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgcont : Continuous g := hg.continuous
  have hdcont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  obtain ⟨M1, hM1⟩ := hgcont.bounded_above_of_compact_support hgc
  obtain ⟨M2, hM2⟩ := hdcont.bounded_above_of_compact_support hgc.deriv
  set M := max M1 M2 with hMdef
  have hgM : ∀ x, |g x| ≤ M := fun x => by
    have := hM1 x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hdM : ∀ x, |deriv g x| ≤ M := fun x => by
    have := hM2 x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_right _ _)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hgM 0)
  have hg2M : ∀ x, g x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hgM x) 2
  have hd2M : ∀ x, deriv g x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdM x) 2
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [ε]; rw [div_le_one (by positivity)]
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f : ℕ → ℝ → ℝ := fun n x => g x ^ 2 + ε n
  have hf_deriv : ∀ n x, deriv (f n) x = 2 * g x * deriv g x := by
    intro n x
    have := (((hgd x).hasDerivAt.pow 2).add_const (ε n))
    exact this.deriv.trans (by simp)
  have hf_contDiff : ∀ n, ContDiff ℝ 1 (f n) := fun n => (hg.pow 2).add contDiff_const
  have hfcont : ∀ n, Continuous (f n) := fun n => (hf_contDiff n).continuous
  -- the bounded-below inequality for `f n`
  have hineq : ∀ n, ∫ x, f n x * Real.log (f n x) ∂(gaussianReal 0 1)
      - (∫ x, f n x ∂(gaussianReal 0 1)) * Real.log (∫ x, f n x ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
    intro n
    have h := gaussian_logsobolev_bounded_below (f n) (hf_contDiff n) (ε n) (3 * M ^ 2 + 1)
      (hε n) (fun x => by simp only [f]; linarith [sq_nonneg (g x)])
      (fun x => by simp only [f]; linarith [hg2M x, hε1 n, sq_nonneg M])
      (fun x => by
        rw [hf_deriv, abs_mul, abs_mul, abs_two]
        have := mul_le_mul (hgM x) (hdM x) (abs_nonneg _) hM0
        nlinarith [sq_nonneg M])
    refine h.trans ?_
    have hle : ∫ x, deriv (f n) x ^ 2 / f n x ∂(gaussianReal 0 1)
        ≤ ∫ x, 4 * deriv g x ^ 2 ∂(gaussianReal 0 1) := by
      refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
        (Eventually.of_forall (fun x => ?_))
      · exact div_nonneg (sq_nonneg _) (by simp only [f]; linarith [sq_nonneg (g x), hε n])
      · refine Integrable.mono' (integrable_const (4 * M ^ 2))
          ((hdcont.pow 2).const_mul 4).aestronglyMeasurable
          (Eventually.of_forall (fun x => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        linarith [hd2M x]
      · simp only
        rw [hf_deriv, div_le_iff₀ (by simp only [f]; linarith [sq_nonneg (g x), hε n])]
        simp only [f]
        nlinarith [mul_nonneg (sq_nonneg (deriv g x)) (hε n).le]
    rw [integral_const_mul] at hle
    linarith
  -- limits as `n → ∞`
  have hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x ^ 2)) := fun x => by
    simpa using (tendsto_const_nhds (x := g x ^ 2)).add hεlim
  have hfb : ∀ n x, 0 ≤ f n x ∧ f n x ≤ M ^ 2 + 1 := fun n x => by
    simp only [f]; constructor <;> linarith [sq_nonneg (g x), hg2M x, hε n, hε1 n]
  have L1 : Tendsto (fun n => ∫ x, f n x ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M ^ 2 + 1)
      (fun n => (hfcont n).aestronglyMeasurable) (integrable_const _) (fun n => ?_)
      (Eventually.of_forall hpt)
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfb n x).1]; exact (hfb n x).2
  have L2 : Tendsto (fun n => ∫ x, f n x * Real.log (f n x) ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (M ^ 2 + 1) ^ 2 + 1)
      (fun n => ((hfcont n).measurable.mul (hfcont n).measurable.log).aestronglyMeasurable)
      (integrable_const _) (fun n => ?_) ?_
    · refine Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_mul_log_le_sq_add_one _ (hfb n x).1).trans ?_
      have := pow_le_pow_left₀ (hfb n x).1 (hfb n x).2 2
      linarith
    · exact Eventually.of_forall (fun x => (Real.continuous_mul_log.tendsto _).comp (hpt x))
  have L4 : Tendsto (fun n => (∫ x, f n x ∂(gaussianReal 0 1))
        * Real.log (∫ x, f n x ∂(gaussianReal 0 1))) atTop
      (𝓝 ((∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1)))) :=
    (Real.continuous_mul_log.tendsto _).comp L1
  exact le_of_tendsto' (L2.sub L4) hineq

/-! ## Main theorem -/

namespace GaussianMatrix

open Filter Topology

/-- `|(G s) log (G s)| ≤ |G log G| + G` for `G ≥ 0` and `s ∈ [0,1]`. -/
lemma mul_log_cutoff_bound (G s : ℝ) (hG : 0 ≤ G) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |G * s * Real.log (G * s)| ≤ |G * Real.log G| + G := by
  rcases hG.eq_or_lt with h | hG'
  · subst h; simp
  rcases hs0.eq_or_lt with h | hs'
  · subst h; simp; positivity
  rw [Real.log_mul hG'.ne' hs'.ne']
  have e : G * s * (Real.log G + Real.log s) = s * (G * Real.log G) + G * (Real.log s * s) := by
    ring
  rw [e]
  have h1 := Real.abs_log_mul_self_lt s hs' hs1
  calc |s * (G * Real.log G) + G * (Real.log s * s)|
      ≤ |s * (G * Real.log G)| + |G * (Real.log s * s)| := abs_add_le _ _
    _ = s * |G * Real.log G| + G * |Real.log s * s| := by
        rw [abs_mul s (G * Real.log G), abs_mul G (Real.log s * s), abs_of_nonneg hs0,
          abs_of_nonneg hG]
    _ ≤ 1 * |G * Real.log G| + G * 1 := by
        gcongr
    _ = |G * Real.log G| + G := by ring

end GaussianMatrix

open GaussianMatrix Filter Topology

theorem solution (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun t => g t ^ 2) (gaussianReal 0 1))
    (hglog : Integrable (fun t => g t ^ 2 * Real.log (g t ^ 2)) (gaussianReal 0 1))
    (hdg : Integrable (fun t => deriv g t ^ 2) (gaussianReal 0 1)) :
    ∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1)
      - (∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
  -- a fixed smooth cutoff `χ`, equal to `1` on `[-1,1]` and supported in `[-2,2]`
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hχc : ContDiff ℝ 1 (fun x => χ x) := χ.contDiff
  have hχd : Continuous (deriv (fun x => χ x)) := hχc.continuous_deriv le_rfl
  have hχs : HasCompactSupport (deriv (fun x => χ x)) := χ.hasCompactSupport.deriv
  obtain ⟨K, hK⟩ := hχd.bounded_above_of_compact_support hχs
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgc : Continuous g := hg.continuous
  -- the truncations `g_n = g · χ(·/(n+1))`
  let c : ℕ → ℝ → ℝ := fun n x => χ (x / ((n : ℝ) + 1))
  let gn : ℕ → ℝ → ℝ := fun n x => g x * c n x
  have hnpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hc_contDiff : ∀ n, ContDiff ℝ 1 (c n) := fun n =>
    hχc.comp (contDiff_id.div_const _)
  have hc01 : ∀ n x, 0 ≤ c n x ∧ c n x ≤ 1 := fun n x => ⟨χ.nonneg, χ.le_one⟩
  have hc_one : ∀ (n : ℕ) (x : ℝ), |x| < (n : ℝ) + 1 → c n x = 1 := by
    intro n x hx
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_div,
      abs_of_pos (hnpos n), div_le_one (hnpos n)]
    exact hx.le
  have hgn_contDiff : ∀ n, ContDiff ℝ 1 (gn n) := fun n => hg.mul (hc_contDiff n)
  have hgn_supp : ∀ n, HasCompactSupport (gn n) := by
    intro n
    apply HasCompactSupport.mul_left
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * ((n : ℝ) + 1)))
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    apply χ.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos (hnpos n),
      le_div_iff₀ (hnpos n)]
    exact hx.le
  -- derivative of the truncation
  have hc_deriv : ∀ n x, deriv (c n) x = deriv (fun x => χ x) (x / ((n : ℝ) + 1))
      / ((n : ℝ) + 1) := by
    intro n x
    have h1 : HasDerivAt (fun x : ℝ => x / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) x :=
      (hasDerivAt_id x).div_const _
    have h2 := ((hχc.differentiable one_ne_zero) (x / ((n : ℝ) + 1))).hasDerivAt.comp x h1
    exact h2.deriv.trans (by ring)
  have hc_deriv_bound : ∀ n x, |deriv (c n) x| ≤ K := by
    intro n x
    rw [hc_deriv, abs_div, abs_of_pos (hnpos n)]
    have := hK (x / ((n : ℝ) + 1))
    rw [Real.norm_eq_abs] at this
    calc |deriv (fun x => χ x) (x / (↑n + 1))| / (↑n + 1) ≤ K / 1 := by
          gcongr
          · linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      _ = K := div_one K
  have hgn_deriv : ∀ n x, deriv (gn n) x = deriv g x * c n x + g x * deriv (c n) x := by
    intro n x
    exact ((hgd x).hasDerivAt.mul
      (((hc_contDiff n).differentiable one_ne_zero) x).hasDerivAt).deriv
  have hgn_deriv_sq : ∀ n x, deriv (gn n) x ^ 2 ≤ 2 * deriv g x ^ 2 + 2 * K ^ 2 * g x ^ 2 := by
    intro n x
    rw [hgn_deriv]
    obtain ⟨h0, h1⟩ := hc01 n x
    have hb := hc_deriv_bound n x
    have hc2 : c n x ^ 2 ≤ 1 := by nlinarith
    have e1 : (deriv g x * c n x) ^ 2 ≤ deriv g x ^ 2 := by
      rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg (deriv g x))]
    have hd2 : deriv (c n) x ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have e2 : (g x * deriv (c n) x) ^ 2 ≤ K ^ 2 * g x ^ 2 := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
    nlinarith [sq_nonneg (deriv g x * c n x - g x * deriv (c n) x)]
  -- pointwise eventual equality
  have hev : ∀ x, ∀ᶠ n in atTop, gn n x = g x ∧ deriv (gn n) x = deriv g x := by
    intro x
    refine eventually_atTop.2 ⟨⌈|x|⌉₊, fun n hn => ?_⟩
    have hx : |x| < (n : ℝ) + 1 := by
      have := Nat.le_ceil |x|
      have : (⌈|x|⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    refine ⟨by show g x * c n x = g x; rw [hc_one n x hx, mul_one], ?_⟩
    have : gn n =ᶠ[𝓝 x] g := by
      have hopen : IsOpen {y : ℝ | |y| < (n : ℝ) + 1} :=
        isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds hx] with y hy
      show g y * c n y = g y; rw [hc_one n y hy, mul_one]
    exact this.deriv_eq
  -- apply the compactly supported inequality to `g_n`
  have hineq : ∀ n, ∫ t, gn n t ^ 2 * Real.log (gn n t ^ 2) ∂(gaussianReal 0 1)
      - (∫ t, gn n t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, gn n t ^ 2 ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv (gn n) t ^ 2 ∂(gaussianReal 0 1) := fun n =>
    gaussian_logsobolev_one_dim_compact_support (gn n) (hgn_contDiff n) (hgn_supp n)
  have hgn_cont : ∀ n, Continuous (gn n) := fun n => (hgn_contDiff n).continuous
  -- limits
  have L1 : Tendsto (fun n => ∫ t, gn n t ^ 2 ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun t => g t ^ 2)
      (fun n => ((hgn_cont n).pow 2).aestronglyMeasurable) hg2 (fun n => ?_) ?_
    · refine Eventually.of_forall (fun x => ?_)
      obtain ⟨h0, h1⟩ := hc01 n x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [gn, mul_pow]
      have hc2 : c n x ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg (g x))]
    · refine Eventually.of_forall (fun x => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [hn.1]
  have L2 : Tendsto (fun n => ∫ t, gn n t ^ 2 * Real.log (gn n t ^ 2) ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun t => |g t ^ 2 * Real.log (g t ^ 2)| + g t ^ 2)
      (fun n => (((hgn_cont n).pow 2).measurable.mul
        ((hgn_cont n).pow 2).measurable.log).aestronglyMeasurable) (hglog.abs.add hg2)
      (fun n => ?_) ?_
    · refine Eventually.of_forall (fun x => ?_)
      obtain ⟨h0, h1⟩ := hc01 n x
      rw [Real.norm_eq_abs]
      have e : gn n x ^ 2 = g x ^ 2 * c n x ^ 2 := by simp only [gn, mul_pow]
      rw [e]
      exact mul_log_cutoff_bound _ _ (sq_nonneg _) (sq_nonneg _) (by nlinarith)
    · refine Eventually.of_forall (fun x => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [hn.1]
  have L3 : Tendsto (fun n => ∫ t, deriv (gn n) t ^ 2 ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun t => 2 * deriv g t ^ 2 + 2 * K ^ 2 * g t ^ 2)
      (fun n => ((measurable_deriv _).pow_const 2).aestronglyMeasurable)
      ((hdg.const_mul 2).add (hg2.const_mul _)) (fun n => ?_) ?_
    · refine Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hgn_deriv_sq n x
    · refine Eventually.of_forall (fun x => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [hn.2]
  have L4 : Tendsto (fun n => (∫ t, gn n t ^ 2 ∂(gaussianReal 0 1))
        * Real.log (∫ t, gn n t ^ 2 ∂(gaussianReal 0 1))) atTop
      (𝓝 ((∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1)))) :=
    (Real.continuous_mul_log.tendsto _).comp L1
  exact le_of_tendsto_of_tendsto' (L2.sub L4) (L3.const_mul 2) hineq
