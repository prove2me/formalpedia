-- Prove2me | solution 1 for GaussianMatrix.ou_entropy_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:18:20.721662+00:00
-- url     : https://prove2.me/submissions/0d3c76e8-2ee8-451e-87f7-f0cfb09d4386

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_ou_semigroup_commutation
import Theorems.Thm_GaussianMatrix_gaussian_ibp_one_dim

open MeasureTheory ProbabilityTheory
open scoped Matrix

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

theorem solution (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (δ C : ℝ) (hδ : 0 < δ)
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
