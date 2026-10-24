-- Prove2me | solution 1 for FreeSamples.Revenue.lemma_4b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T01:35:14.221907+00:00
-- url     : https://prove2.me/submissions/fbb038b0-898b-4599-9ab9-273ad9b6d9e6

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace FS4bAux
open FreeSamples.Revenue

/-! ### Part 1: partial derivatives of a `C²` function on `ℝ × (0,∞)` -/

lemma isOpen_U : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0:ℝ)) := isOpen_univ.prod isOpen_Ioi

lemma mem_U {x v : ℝ} (hv : 0 < v) : ((x, v) : ℝ × ℝ) ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioi (0:ℝ) :=
  ⟨trivial, hv⟩

section Calc
variable (F : ℝ → ℝ → ℝ)
  (hC : ContDiffOn ℝ 2 (Function.uncurry F) (Set.univ ×ˢ Set.Ioi 0))
include hC

lemma diffAt {x v : ℝ} (hv : 0 < v) : DifferentiableAt ℝ (Function.uncurry F) (x, v) :=
  (hC.differentiableOn (by norm_num)).differentiableAt
    ((isOpen_U).mem_nhds (mem_U hv))

lemma diffAt_fderiv {x v : ℝ} (hv : 0 < v) :
    DifferentiableAt ℝ (fderiv ℝ (Function.uncurry F)) (x, v) :=
  ((hC.fderiv_of_isOpen isOpen_U (m := 1) (by norm_num)).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_U).mem_nhds (mem_U hv))

lemma hasDerivAt_slice {x v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun y => F y v) (fderiv ℝ (Function.uncurry F) (x, v) (1, 0)) x := by
  have h1 : HasDerivAt (fun y : ℝ => ((y, v) : ℝ × ℝ)) ((1:ℝ), (0:ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x v)
  have := (diffAt F hC hv).hasFDerivAt.comp_hasDerivAt x h1
  simpa [Function.comp_def] using this

lemma dθ_eq {x v : ℝ} (hv : 0 < v) :
    dθ F x v = fderiv ℝ (Function.uncurry F) (x, v) (1, 0) :=
  (hasDerivAt_slice F hC hv).deriv

lemma hasDerivAt_slice' {x v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun y => fderiv ℝ (Function.uncurry F) (y, v) (1, 0))
      (fderiv ℝ (fderiv ℝ (Function.uncurry F)) (x, v) (1, 0) (1, 0)) x := by
  have h1 : HasDerivAt (fun y : ℝ => ((y, v) : ℝ × ℝ)) ((1:ℝ), (0:ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x v)
  have h2 := (diffAt_fderiv F hC hv (x := x)).hasFDerivAt.comp_hasDerivAt x h1
  have h3 := h2.clm_apply (hasDerivAt_const x ((1:ℝ), (0:ℝ)))
  simpa [Function.comp_def] using h3

lemma dθθ_eq {x v : ℝ} (hv : 0 < v) :
    dθθ F x v = fderiv ℝ (fderiv ℝ (Function.uncurry F)) (x, v) (1, 0) (1, 0) := by
  unfold dθθ
  have : (fun x' => deriv (fun y => F y v) x') =
      fun y => fderiv ℝ (Function.uncurry F) (y, v) (1, 0) := by
    funext x'; exact (hasDerivAt_slice F hC hv).deriv
  rw [this]
  exact (hasDerivAt_slice' F hC hv).deriv

lemma hasDerivAt_dθ {x v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun y => dθ F y v) (dθθ F x v) x := by
  rw [dθθ_eq F hC hv]
  have : (fun y => dθ F y v) = fun y => fderiv ℝ (Function.uncurry F) (y, v) (1, 0) := by
    funext y; exact dθ_eq F hC hv
  rw [this]
  exact hasDerivAt_slice' F hC hv

lemma hasDerivAt_F {x v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun y => F y v) (dθ F x v) x := by
  rw [dθ_eq F hC hv]; exact hasDerivAt_slice F hC hv

lemma continuous_slice {v : ℝ} (hv : 0 < v) : Continuous (fun y => F y v) :=
  continuous_iff_continuousAt.2 fun _ => (hasDerivAt_F F hC hv).continuousAt

lemma continuousAt_d2 {a v₀ : ℝ} (hv₀ : 0 < v₀) :
    ContinuousAt (fun p : ℝ × ℝ => fderiv ℝ (fderiv ℝ (Function.uncurry F)) p (1, 0) (1, 0))
      (a, v₀) := by
  have hc : ContinuousOn (fun p => fderiv ℝ (fderiv ℝ (Function.uncurry F)) p)
      (Set.univ ×ˢ Set.Ioi (0:ℝ)) :=
    (hC.fderiv_of_isOpen isOpen_U (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
      isOpen_U (by norm_num)
  have := (hc.continuousAt ((isOpen_U).mem_nhds (mem_U (x := a) hv₀)))
  exact (this.clm_apply continuousAt_const).clm_apply continuousAt_const

lemma continuousAt_d1 {a v₀ : ℝ} (hv₀ : 0 < v₀) :
    ContinuousAt (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry F) p (1, 0)) (a, v₀) := by
  have hc : ContinuousOn (fun p => fderiv ℝ (Function.uncurry F) p)
      (Set.univ ×ˢ Set.Ioi (0:ℝ)) :=
    hC.continuousOn_fderiv_of_isOpen isOpen_U (by norm_num)
  exact (hc.continuousAt ((isOpen_U).mem_nhds (mem_U (x := a) hv₀))).clm_apply continuousAt_const

/-- joint continuity of `dθθ` at `(a, v₀)` in ε-δ form. -/
lemma dθθ_cont {a v₀ : ℝ} (hv₀ : 0 < v₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x v, |x - a| < δ → |v - v₀| < δ → 0 < v ∧ |dθθ F x v - dθθ F a v₀| < ε := by
  have hc := continuousAt_d2 F hC (a := a) hv₀
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc ε hε
  refine ⟨min δ v₀, lt_min hδ hv₀, fun x v hx hv => ?_⟩
  have hvpos : 0 < v := by
    have := lt_of_lt_of_le hv (min_le_right _ _)
    rw [abs_lt] at this; linarith
  refine ⟨hvpos, ?_⟩
  rw [dθθ_eq F hC hvpos, dθθ_eq F hC hv₀]
  have := hδ' (x := (x, v)) (by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    exact ⟨lt_of_lt_of_le hx (min_le_left _ _), lt_of_lt_of_le hv (min_le_left _ _)⟩)
  rwa [Real.dist_eq] at this

lemma tendsto_dθ_a {a v₀ : ℝ} (hv₀ : 0 < v₀) :
    Tendsto (fun v => dθ F a v) (𝓝 v₀) (𝓝 (dθ F a v₀)) := by
  have h1 : ContinuousAt (fun v => fderiv ℝ (Function.uncurry F) (a, v) (1, 0)) v₀ :=
    (continuousAt_d1 F hC (a := a) hv₀).comp (f := fun v : ℝ => ((a, v) : ℝ × ℝ))
      (continuousAt_const.prodMk continuousAt_id)
  have heq : (fun v => dθ F a v) =ᶠ[𝓝 v₀] fun v => fderiv ℝ (Function.uncurry F) (a, v) (1, 0) := by
    filter_upwards [lt_mem_nhds hv₀] with v hv using dθ_eq F hC hv
  exact (h1.congr heq.symm).tendsto

lemma tendsto_dθθ_a {a v₀ : ℝ} (hv₀ : 0 < v₀) :
    Tendsto (fun v => dθθ F a v) (𝓝 v₀) (𝓝 (dθθ F a v₀)) := by
  have h1 : ContinuousAt
      (fun v => fderiv ℝ (fderiv ℝ (Function.uncurry F)) (a, v) (1, 0) (1, 0)) v₀ :=
    (continuousAt_d2 F hC (a := a) hv₀).comp (f := fun v : ℝ => ((a, v) : ℝ × ℝ))
      (continuousAt_const.prodMk continuousAt_id)
  have heq : (fun v => dθθ F a v) =ᶠ[𝓝 v₀]
      fun v => fderiv ℝ (fderiv ℝ (Function.uncurry F)) (a, v) (1, 0) (1, 0) := by
    filter_upwards [lt_mem_nhds hv₀] with v hv using dθθ_eq F hC hv
  exact (h1.congr heq.symm).tendsto

lemma hasDerivAt_dv {a v₀ : ℝ} (hv₀ : 0 < v₀) :
    HasDerivAt (fun w => F a w) (dv F a v₀) v₀ := by
  have h1 : DifferentiableAt ℝ (fun w : ℝ => ((a, w) : ℝ × ℝ)) v₀ := by fun_prop
  have : DifferentiableAt ℝ (fun w => F a w) v₀ := by
    have := (diffAt F hC (x := a) hv₀).comp v₀ h1
    simpa [Function.comp_def] using this
  exact this.hasDerivAt

end Calc

/-! ### Part 2: a second-order Taylor bound -/

lemma taylor2_bound (g g' g'' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (a x ε : ℝ)
    (hε : ∀ y ∈ Set.uIcc a x, |g'' y - g'' a| ≤ ε) :
    |g x - g a - g' a * (x - a) - (1/2) * g'' a * (x - a) ^ 2| ≤ ε * (x - a) ^ 2 := by
  set K : ℝ → ℝ := fun y => g y - g a - g' a * (y - a) - (1/2) * g'' a * (y - a) ^ 2 with hKdef
  set K' : ℝ → ℝ := fun y => g' y - g' a - g'' a * (y - a) with hK'def
  have hK : ∀ y, HasDerivAt K (K' y) y := by
    intro y
    have := ((((hg y).sub_const (g a)).sub ((hasDerivAt_id y).sub_const a |>.const_mul (g' a))).sub
      ((((hasDerivAt_id y).sub_const a).pow 2).const_mul ((1/2) * g'' a)))
    refine this.congr_deriv ?_
    rw [hK'def]; simp only [id]; push_cast; ring
  have hK' : ∀ y, HasDerivAt K' (g'' y - g'' a) y := by
    intro y
    have := ((hg' y).sub_const (g' a)).sub (((hasDerivAt_id y).sub_const a).const_mul (g'' a))
    refine this.congr_deriv ?_
    ring
  -- step 1
  have step1 : ∀ y ∈ Set.uIcc a x, |K' y| ≤ ε * |x - a| := by
    intro y hy
    have hsub : Set.uIcc a y ⊆ Set.uIcc a x :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc hy
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := K') (f' := fun y => g'' y - g'' a) (s := Set.uIcc a y) (C := ε)
      (fun z _ => (hK' z).hasDerivWithinAt) (fun z hz => by
        simpa [Real.norm_eq_abs] using hε z (hsub hz)) (convex_uIcc a y)
      Set.left_mem_uIcc Set.right_mem_uIcc
    have hKa : K' a = 0 := by simp [K']
    rw [hKa, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
    have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hε a Set.left_mem_uIcc)
    calc |K' y| ≤ ε * |y - a| := this
      _ ≤ ε * |x - a| := mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc (h := hy)) hε0
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := K) (f' := K') (s := Set.uIcc a x) (C := ε * |x - a|)
      (fun z _ => (hK z).hasDerivWithinAt) (fun z hz => by
        simpa [Real.norm_eq_abs] using step1 z hz) (convex_uIcc a x)
      Set.left_mem_uIcc Set.right_mem_uIcc
  have hKa : K a = 0 := by simp [K]
  rw [hKa, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
  calc _ = |K x| := rfl
    _ ≤ ε * |x - a| * |x - a| := this
    _ = ε * (x - a) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-! ### Part 3: Gaussian integrals -/

lemma integrable_exp_abs (t : ℝ) :
    Integrable (fun z : ℝ => Real.exp (t * |z|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_gaussianReal t).add (integrable_exp_mul_gaussianReal (-t))).mono'
    (by fun_prop) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  show _ ≤ Real.exp (t * z) + Real.exp (-t * z)
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]; have := Real.exp_pos (-t * z); linarith
  · rw [abs_of_nonpos hz]; have := Real.exp_pos (t * z)
    have : t * -z = -t * z := by ring
    rw [this]; linarith

lemma sq_le_exp (z : ℝ) : z ^ 2 ≤ 2 * Real.exp |z| := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg z)
  have : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
  nlinarith [abs_nonneg z]

lemma pow4_le_exp (z : ℝ) : z ^ 4 ≤ 24 * Real.exp |z| := by
  have h := Real.pow_div_factorial_le_exp (x := |z|) (abs_nonneg z) 4
  have h4 : z ^ 4 = |z| ^ 4 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h4]
  norm_num [Nat.factorial] at h
  linarith



lemma integrable_z2 : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) :=
  ((integrable_exp_abs 1).const_mul 2).mono' (by fun_prop) (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z), one_mul]; exact sq_le_exp z)

lemma integrable_z : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
  ((integrable_z2).add (integrable_const 1)).mono' (by fun_prop) (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs]
    show |z| ≤ z ^ 2 + 1
    nlinarith [abs_nonneg z, sq_abs z])

lemma integrable_z4exp (b : ℝ) : Integrable (fun z : ℝ => z ^ 4 * Real.exp (b * |z|)) (gaussianReal 0 1) :=
  ((integrable_exp_abs (b + 1)).const_mul 24).mono' (by fun_prop) (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := pow4_le_exp z
    have h2 : Real.exp ((b + 1) * |z|) = Real.exp |z| * Real.exp (b * |z|) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)

lemma int_z : ∫ z, z ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

lemma int_z2 : ∫ z, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at this
  simpa [integral_id_gaussianReal] using this

lemma int_quad (c0 c1 c2 : ℝ) : ∫ z, (c0 + c1 * z + c2 * z ^ 2) ∂(gaussianReal 0 1) = c0 + c2 := by
  have i1 : Integrable (fun z : ℝ => c0 + c1 * z) (gaussianReal 0 1) :=
    (integrable_const _).add (integrable_z.const_mul _)
  have i2 : Integrable (fun z : ℝ => c2 * z ^ 2) (gaussianReal 0 1) := integrable_z2.const_mul _
  rw [integral_add (f := fun z : ℝ => c0 + c1 * z) (g := fun z : ℝ => c2 * z ^ 2) i1 i2,
    integral_add (f := fun _ : ℝ => c0) (g := fun z : ℝ => c1 * z) (integrable_const _)
      (integrable_z.const_mul _), integral_const_mul,
    integral_const_mul, int_z, int_z2]
  simp

lemma integrable_quad (c0 c1 c2 : ℝ) : Integrable (fun z : ℝ => c0 + c1 * z + c2 * z ^ 2) (gaussianReal 0 1) :=
  ((integrable_const _).add (integrable_z.const_mul _)).add (integrable_z2.const_mul _)

/-! ### Part 4: the Taylor remainder estimates -/

/-- The second-order Taylor remainder of `F(·, v)` at `a`. -/
noncomputable def Rf (F : ℝ → ℝ → ℝ) (a x v : ℝ) : ℝ :=
  F x v - F a v - dθ F a v * (x - a) - (1/2) * dθθ F a v * (x - a) ^ 2

lemma R_glob (F : ℝ → ℝ → ℝ) (a v₀ : ℝ) (hv : 0 < v₀)
    (hG : ∃ C c : ℝ, ∀ θ, ∀ v ∈ Set.Ioc 0 v₀,
      |F θ v| + |dθ F θ v| + |dθθ F θ v| + |dv F θ v| ≤ C * Real.exp (c * |θ|)) :
    ∃ K₀ b : ℝ, 0 ≤ K₀ ∧ 0 ≤ b ∧ ∀ x v, 0 < v → v ≤ v₀ →
      |Rf F a x v| ≤ K₀ * Real.exp (b * |x - a|) := by
  obtain ⟨C, c, hb⟩ := hG
  set c₁ := |c|
  have hc₁ : 0 ≤ c₁ := abs_nonneg c
  have hb' : ∀ θ, ∀ v ∈ Set.Ioc 0 v₀,
      |F θ v| + |dθ F θ v| + |dθθ F θ v| + |dv F θ v| ≤ C * Real.exp (c₁ * |θ|) := by
    intro θ v hv
    refine (hb θ v hv).trans ?_
    have hC0 : 0 ≤ C := by
      have := (hb θ v hv)
      have h0 : 0 ≤ C * Real.exp (c * |θ|) := le_trans (by positivity) this
      exact nonneg_of_mul_nonneg_left h0 (Real.exp_pos _)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0
    exact mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg _)
  refine ⟨3 * C * Real.exp (c₁ * |a|), c₁ + 1, ?_, by linarith, ?_⟩
  · have := hb' a v₀ ⟨hv, le_rfl⟩
    have h0 : 0 ≤ C * Real.exp (c₁ * |a|) := le_trans (by positivity) this
    have : 0 ≤ C := nonneg_of_mul_nonneg_left h0 (Real.exp_pos _)
    positivity
  · intro x v hv hvv
    have hx := hb' x v ⟨hv, hvv⟩
    have ha := hb' a v ⟨hv, hvv⟩
    set E := Real.exp (c₁ * |a|)
    set t := |x - a|
    have ht : 0 ≤ t := abs_nonneg _
    have hFx : |F x v| ≤ C * Real.exp (c₁ * |x|) := by
      have := abs_nonneg (dθ F x v); have := abs_nonneg (dθθ F x v)
      have := abs_nonneg (dv F x v); linarith
    have hFa : |F a v| ≤ C * E := by
      have := abs_nonneg (dθ F a v); have := abs_nonneg (dθθ F a v)
      have := abs_nonneg (dv F a v); linarith
    have hDa : |dθ F a v| ≤ C * E := by
      have := abs_nonneg (F a v); have := abs_nonneg (dθθ F a v)
      have := abs_nonneg (dv F a v); linarith
    have hDDa : |dθθ F a v| ≤ C * E := by
      have := abs_nonneg (F a v); have := abs_nonneg (dθ F a v)
      have := abs_nonneg (dv F a v); linarith
    have hCE : 0 ≤ C * E := le_trans (abs_nonneg _) hFa
    have hexpx : Real.exp (c₁ * |x|) ≤ E * Real.exp (c₁ * t) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      have : |x| ≤ |a| + t := by
        calc |x| = |a + (x - a)| := by ring_nf
          _ ≤ |a| + |x - a| := abs_add_le _ _
      nlinarith
    have hC0 : 0 ≤ C := by
      by_contra hneg; push Not at hneg
      have : C * E < 0 := mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
      linarith
    have hquad : 1 + t + t ^ 2 / 2 ≤ Real.exp t := Real.quadratic_le_exp_of_nonneg ht
    have he1 : Real.exp (c₁ * t) ≤ Real.exp ((c₁ + 1) * t) := Real.exp_le_exp.2 (by nlinarith)
    have he2 : Real.exp t ≤ Real.exp ((c₁ + 1) * t) := Real.exp_le_exp.2 (by nlinarith)
    unfold Rf
    have hsq : (x - a) ^ 2 = t ^ 2 := (sq_abs _).symm
    calc |F x v - F a v - dθ F a v * (x - a) - 1 / 2 * dθθ F a v * (x - a) ^ 2|
        ≤ |F x v| + |F a v| + |dθ F a v| * t + 1 / 2 * |dθθ F a v| * t ^ 2 := by
          have h1 := abs_sub (F x v - F a v - dθ F a v * (x - a)) (1 / 2 * dθθ F a v * (x - a) ^ 2)
          have h2 := abs_sub (F x v - F a v) (dθ F a v * (x - a))
          have h3 := abs_sub (F x v) (F a v)
          have h4 : |dθ F a v * (x - a)| = |dθ F a v| * t := abs_mul _ _
          have h5 : |1 / 2 * dθθ F a v * (x - a) ^ 2| = 1 / 2 * |dθθ F a v| * t ^ 2 := by
            rw [abs_mul, abs_mul, hsq, abs_of_nonneg (sq_nonneg t)]; norm_num
          linarith
      _ ≤ C * (E * Real.exp (c₁ * t)) + C * E + C * E * t + 1 / 2 * (C * E) * t ^ 2 := by
          have := mul_le_mul_of_nonneg_left hexpx hC0
          have h6 := mul_le_mul_of_nonneg_right hDa ht
          have h7 := mul_le_mul_of_nonneg_right hDDa (sq_nonneg t)
          nlinarith
      _ ≤ 3 * C * E * Real.exp ((c₁ + 1) * t) := by
          have hEe : C * E * (1 + t + t ^ 2 / 2) ≤ C * E * Real.exp t :=
            mul_le_mul_of_nonneg_left hquad hCE
          have h8 := mul_le_mul_of_nonneg_left he1 hCE
          have h9 := mul_le_mul_of_nonneg_left he2 hCE
          nlinarith


lemma R_near (F : ℝ → ℝ → ℝ)
    (hC : ContDiffOn ℝ 2 (Function.uncurry F) (Set.univ ×ˢ Set.Ioi 0))
    {a v₀ : ℝ} (hv₀ : 0 < v₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x v, |x - a| < δ → |v - v₀| < δ → |Rf F a x v| ≤ 2 * ε * (x - a) ^ 2 := by
  obtain ⟨δ, hδ, hcont⟩ := dθθ_cont F hC (a := a) hv₀ hε
  refine ⟨δ, hδ, fun x v hx hv => ?_⟩
  have hvpos : 0 < v := (hcont a v (by simpa using hδ) hv).1
  have h0 := (hcont a v (by simpa using hδ) hv).2
  have := taylor2_bound (fun y => F y v) (fun y => dθ F y v) (fun y => dθθ F y v)
    (fun y => hasDerivAt_F F hC hvpos) (fun y => hasDerivAt_dθ F hC hvpos) a x (2 * ε)
    (fun y hy => by
      have hya : |y - a| < δ := lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc (h := hy)) hx
      have h1 := (hcont y v hya hv).2
      have := abs_sub_le (dθθ F y v) (dθθ F a v₀) (dθθ F a v)
      rw [abs_sub_comm (dθθ F a v₀)] at this
      linarith)
  simpa [Rf] using this

lemma R_comb (F : ℝ → ℝ → ℝ) (a v₀ K₀ b ε δ : ℝ) (hδ : 0 < δ) (hK₀ : 0 ≤ K₀)
    (hglob : ∀ x v, 0 < v → v ≤ v₀ → |Rf F a x v| ≤ K₀ * Real.exp (b * |x - a|))
    (hnear : ∀ x v, |x - a| < δ → |v - v₀| < δ → |Rf F a x v| ≤ 2 * ε * (x - a) ^ 2)
    (hε : 0 ≤ ε) (x v : ℝ) (hv : 0 < v) (hvv : v ≤ v₀) (hvd : |v - v₀| < δ) :
    |Rf F a x v| ≤ 2 * ε * (x - a) ^ 2 + K₀ * Real.exp (b * |x - a|) * (x - a) ^ 4 / δ ^ 4 := by
  have hE : 0 ≤ K₀ * Real.exp (b * |x - a|) := by positivity
  by_cases hx : |x - a| < δ
  · have := hnear x v hx hvd
    have : 0 ≤ K₀ * Real.exp (b * |x - a|) * (x - a) ^ 4 / δ ^ 4 := by positivity
    linarith
  · push Not at hx
    have h4 : δ ^ 4 ≤ (x - a) ^ 4 := by
      have : (x - a) ^ 4 = |x - a| ^ 4 := by
        rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
      rw [this]; exact pow_le_pow_left₀ hδ.le hx 4
    have h1 : 1 ≤ (x - a) ^ 4 / δ ^ 4 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have := hglob x v hv hvv
    have : K₀ * Real.exp (b * |x - a|) ≤ K₀ * Real.exp (b * |x - a|) * (x - a) ^ 4 / δ ^ 4 := by
      rw [mul_div_assoc]; nlinarith
    nlinarith [sq_nonneg (x - a)]

lemma pointP (K₀ b ε δ M s z R : ℝ) (hK₀ : 0 ≤ K₀) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hM : |M| ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hR : |R| ≤ 2 * ε * (M + s * z) ^ 2 +
      K₀ * Real.exp (b * |M + s * z|) * (M + s * z) ^ 4 / δ ^ 4) :
    |R| ≤ 4 * ε * (M ^ 2 + s ^ 2 * z ^ 2) +
      8 * K₀ * Real.exp b / δ ^ 4 * (M ^ 4 * Real.exp (b * |z|) +
        (s ^ 2) ^ 2 * (z ^ 4 * Real.exp (b * |z|))) := by
  have h2 : (M + s * z) ^ 2 ≤ 2 * (M ^ 2 + s ^ 2 * z ^ 2) := by nlinarith [sq_nonneg (M - s * z)]
  have h4 : (M + s * z) ^ 4 ≤ 8 * (M ^ 4 + (s ^ 2) ^ 2 * z ^ 4) := by
    have e : (M + s * z) ^ 4 = ((M + s * z) ^ 2) ^ 2 := by ring
    have h2' : ((M + s * z) ^ 2) ^ 2 ≤ (2 * (M ^ 2 + s ^ 2 * z ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h2 2
    nlinarith [sq_nonneg (M ^ 2 - s ^ 2 * z ^ 2)]
  have habs : |M + s * z| ≤ 1 + |z| := by
    calc |M + s * z| ≤ |M| + |s * z| := abs_add_le _ _
      _ = |M| + s * |z| := by rw [abs_mul, abs_of_nonneg hs0]
      _ ≤ 1 + |z| := by nlinarith [abs_nonneg z]
  have hexp : Real.exp (b * |M + s * z|) ≤ Real.exp b * Real.exp (b * |z|) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
  have hd4 : 0 < δ ^ 4 := by positivity
  have t1 : 2 * ε * (M + s * z) ^ 2 ≤ 4 * ε * (M ^ 2 + s ^ 2 * z ^ 2) := by nlinarith
  have t2 : K₀ * Real.exp (b * |M + s * z|) * (M + s * z) ^ 4 / δ ^ 4 ≤
      8 * K₀ * Real.exp b / δ ^ 4 * (M ^ 4 * Real.exp (b * |z|) +
        (s ^ 2) ^ 2 * (z ^ 4 * Real.exp (b * |z|))) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hd4]
    have hp4 : 0 ≤ (M + s * z) ^ 4 := by positivity
    have := mul_le_mul hexp h4 hp4 (by positivity)
    have := mul_le_mul_of_nonneg_left this hK₀
    nlinarith
  linarith


lemma estimate_arith (ε' A₁ A₂ I₀ I₄ Q h M W : ℝ) (hε' : 0 < ε') (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hI₀ : 0 ≤ I₀) (hI₄ : 0 ≤ I₄) (hQ : 0 ≤ Q) (hh : 0 < h) (hh1 : h < 1)
    (hhη : h < ε' / (4 * (Q * (A₁ ^ 4 * I₀ + A₂ ^ 2 * I₄) + 1)))
    (hM : |M| < A₁ * h) (hW0 : 0 ≤ W) (hW : W < A₂ * h) :
    4 * (ε' / (8 * (A₁ ^ 2 + A₂ + 1))) * (M ^ 2 + W) + Q * (M ^ 4 * I₀ + W ^ 2 * I₄)
      < ε' * h := by
  have hM2 : M ^ 2 ≤ A₁ ^ 2 * h := by
    have : M ^ 2 = |M| ^ 2 := (sq_abs M).symm
    have h1 : |M| ^ 2 ≤ (A₁ * h) ^ 2 := pow_le_pow_left₀ (abs_nonneg M) hM.le 2
    have h2 : (A₁ * h) ^ 2 ≤ A₁ ^ 2 * h := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    linarith
  have hM4 : M ^ 4 ≤ A₁ ^ 4 * h ^ 2 := by
    have : M ^ 4 = (|M| ^ 2) ^ 2 := by rw [sq_abs]; ring
    have h1 : |M| ^ 2 ≤ (A₁ * h) ^ 2 := pow_le_pow_left₀ (abs_nonneg M) hM.le 2
    have h2 : (|M| ^ 2) ^ 2 ≤ ((A₁ * h) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    have h3 : ((A₁ * h) ^ 2) ^ 2 ≤ A₁ ^ 4 * h ^ 2 := by
      have : ((A₁ * h) ^ 2) ^ 2 = A₁ ^ 4 * h ^ 2 * h ^ 2 := by ring
      rw [this]
      have : h ^ 2 ≤ 1 := by nlinarith
      have : 0 ≤ A₁ ^ 4 * h ^ 2 := by positivity
      nlinarith
    linarith
  have hW2 : W ^ 2 ≤ A₂ ^ 2 * h ^ 2 := by
    have := pow_le_pow_left₀ hW0 hW.le 2
    rw [mul_pow] at this; exact this
  set S := A₁ ^ 2 + A₂ + 1
  have hS : 0 < S := by positivity
  have t1 : 4 * (ε' / (8 * S)) * (M ^ 2 + W) ≤ ε' / 2 * h := by
    have : M ^ 2 + W ≤ S * h := by nlinarith
    calc 4 * (ε' / (8 * S)) * (M ^ 2 + W) ≤ 4 * (ε' / (8 * S)) * (S * h) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε' / 2 * h := by field_simp; ring
  set T := Q * (A₁ ^ 4 * I₀ + A₂ ^ 2 * I₄)
  have hT : 0 ≤ T := by positivity
  have t2 : Q * (M ^ 4 * I₀ + W ^ 2 * I₄) ≤ T * h ^ 2 := by
    have : M ^ 4 * I₀ + W ^ 2 * I₄ ≤ (A₁ ^ 4 * I₀ + A₂ ^ 2 * I₄) * h ^ 2 := by
      have := mul_le_mul_of_nonneg_right hM4 hI₀
      have := mul_le_mul_of_nonneg_right hW2 hI₄
      nlinarith
    calc Q * (M ^ 4 * I₀ + W ^ 2 * I₄) ≤ Q * ((A₁ ^ 4 * I₀ + A₂ ^ 2 * I₄) * h ^ 2) :=
          mul_le_mul_of_nonneg_left this hQ
      _ = T * h ^ 2 := by ring
  have t3 : T * h ^ 2 ≤ ε' / 4 * h := by
    have hlt : h * (4 * (T + 1)) < ε' := by
      rw [lt_div_iff₀ (by positivity)] at hhη; linarith
    nlinarith
  nlinarith

theorem keyA (F : ℝ → ℝ → ℝ)
    (hC : ContDiffOn ℝ 2 (Function.uncurry F) (Set.univ ×ˢ Set.Ioi 0))
    (a v₀ : ℝ) (hv₀ : 0 < v₀)
    (hG : ∃ C c : ℝ, ∀ θ, ∀ v ∈ Set.Ioc 0 v₀,
      |F θ v| + |dθ F θ v| + |dθθ F θ v| + |dv F θ v| ≤ C * Real.exp (c * |θ|))
    (m w v : ℝ → ℝ) (m' w' v' : ℝ)
    (hm : Tendsto (fun h => (m h - a) / h) (𝓝[>] 0) (𝓝 m'))
    (hw : Tendsto (fun h => w h / h) (𝓝[>] 0) (𝓝 w'))
    (hw0 : ∀ h > 0, 0 ≤ w h)
    (hv : HasDerivAt v v' 0) (hv0 : v 0 = v₀) (hvpos : ∀ h > 0, 0 < v h ∧ v h ≤ v₀) :
    Tendsto (fun h => ((∫ z, F (m h + √(w h) * z) (v h) ∂(gaussianReal 0 1)) - F a v₀) / h) (𝓝[>] 0)
      (𝓝 (dθ F a v₀ * m' + (1/2) * dθθ F a v₀ * w' + dv F a v₀ * v')) := by
  obtain ⟨K₀, b, hK₀, hb, hglob⟩ := R_glob F a v₀ hv₀ hG
  have hpos : ∀ᶠ h in 𝓝[>] (0:ℝ), 0 < h := self_mem_nhdsWithin
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hvt : Tendsto v (𝓝[>] 0) (𝓝 v₀) := by
    rw [← hv0]; exact hv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hMt : Tendsto (fun h => m h - a) (𝓝[>] 0) (𝓝 0) := by
    have := hid.mul hm
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [hpos] with h hh
    have := hh.ne'
    field_simp
  have hwt : Tendsto w (𝓝[>] 0) (𝓝 0) := by
    have := hid.mul hw
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [hpos] with h hh
    have := hh.ne'
    field_simp
  have hM1 : ∀ᶠ h in 𝓝[>] (0:ℝ), |m h - a| ≤ 1 := by
    have := (Metric.tendsto_nhds.1 hMt) 1 one_pos
    filter_upwards [this] with h hh
    rw [Real.dist_eq, sub_zero] at hh; exact hh.le
  have hw1 : ∀ᶠ h in 𝓝[>] (0:ℝ), w h ≤ 1 := by
    have := (Metric.tendsto_nhds.1 hwt) 1 one_pos
    filter_upwards [this] with h hh
    rw [Real.dist_eq, sub_zero] at hh; exact (le_abs_self _).trans hh.le
  have hL1 : Tendsto (fun h => (F a (v h) - F a v₀) / h) (𝓝[>] 0) (𝓝 (dv F a v₀ * v')) := by
    have hd2 : HasDerivAt (fun w => F a w) (dv F a v₀) (v 0) := by
      rw [hv0]; exact hasDerivAt_dv F hC hv₀
    have hd := hd2.comp 0 hv
    have := hd.tendsto_slope_zero_right
    refine this.congr' ?_
    filter_upwards with h
    simp [Function.comp_def, hv0, div_eq_inv_mul]
  -- the remainder
  have hR : Tendsto (fun h => (∫ z, Rf F a (m h + √(w h) * z) (v h) ∂(gaussianReal 0 1)) / h) (𝓝[>] 0)
      (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε' hε'
    set A₁ := |m'| + 1
    set A₂ := |w'| + 1
    have hA₁0 : 0 ≤ A₁ := by positivity
    have hA₂0 : 0 ≤ A₂ := by positivity
    have hA₁ : ∀ᶠ h in 𝓝[>] (0:ℝ), |(m h - a) / h| < A₁ :=
      (hm.abs).eventually (gt_mem_nhds (by linarith))
    have hA₂ : ∀ᶠ h in 𝓝[>] (0:ℝ), w h / h < A₂ :=
      hw.eventually (gt_mem_nhds (by linarith [le_abs_self w']))
    set I₀ := ∫ z, Real.exp (b * |z|) ∂(gaussianReal 0 1)
    set I₄ := ∫ z, z ^ 4 * Real.exp (b * |z|) ∂(gaussianReal 0 1)
    have hI₀ : 0 ≤ I₀ := integral_nonneg (fun z => (Real.exp_pos _).le)
    have hI₄ : 0 ≤ I₄ := integral_nonneg (fun z => by positivity)
    set ε := ε' / (8 * (A₁ ^ 2 + A₂ + 1))
    have hε : 0 < ε := by positivity
    obtain ⟨δ, hδ, hnear⟩ := R_near F hC (a := a) hv₀ hε
    set Q := 8 * K₀ * Real.exp b / δ ^ 4
    have hQ : 0 ≤ Q := by positivity
    set η := ε' / (4 * (Q * (A₁ ^ 4 * I₀ + A₂ ^ 2 * I₄) + 1))
    have hη : 0 < η := by positivity
    have hvd : ∀ᶠ h in 𝓝[>] (0:ℝ), |v h - v₀| < δ := by
      have := (Metric.tendsto_nhds.1 hvt) δ hδ
      filter_upwards [this] with h hh
      rwa [Real.dist_eq] at hh
    have hh1 : ∀ᶠ h in 𝓝[>] (0:ℝ), h < min 1 η := by
      have := (Metric.tendsto_nhds.1 hid) (min 1 η) (by positivity)
      filter_upwards [this] with h hh
      rw [Real.dist_eq, sub_zero] at hh; exact lt_of_abs_lt hh
    filter_upwards [hpos, hA₁, hA₂, hvd, hM1, hw1, hh1] with h hh hA1 hA2 hvdh hM1h hw1h hh1h
    set M := m h - a with hMdef
    set W := w h with hWdef
    have hW0 : 0 ≤ W := hw0 h hh
    set s := √W with hsdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : s ≤ 1 := by
      have := Real.sqrt_le_sqrt hw1h; rwa [Real.sqrt_one] at this
    have hs2 : s ^ 2 = W := Real.sq_sqrt hW0
    obtain ⟨hvp, hvle⟩ := hvpos h hh
    have hpt : ∀ z, ‖Rf F a (m h + s * z) (v h)‖ ≤ 4 * ε * (M ^ 2 + s ^ 2 * z ^ 2) +
        Q * (M ^ 4 * Real.exp (b * |z|) + (s ^ 2) ^ 2 * (z ^ 4 * Real.exp (b * |z|))) := by
      intro z
      have := R_comb F a v₀ K₀ b ε δ hδ hK₀ hglob hnear hε.le (m h + s * z) (v h) hvp hvle hvdh
      have e : m h + s * z - a = M + s * z := by rw [hMdef]; ring
      rw [e] at this
      rw [Real.norm_eq_abs]
      exact pointP K₀ b ε δ M s z _ hK₀ hb hε.le hδ hM1h hs0 hs1 this
    have hPint : Integrable (fun z => 4 * ε * (M ^ 2 + s ^ 2 * z ^ 2) +
        Q * (M ^ 4 * Real.exp (b * |z|) + (s ^ 2) ^ 2 * (z ^ 4 * Real.exp (b * |z|)))) (gaussianReal 0 1) := by
      refine (((integrable_const _).add (integrable_z2.const_mul _)).const_mul _).add ?_
      exact (((integrable_exp_abs b).const_mul _).add ((integrable_z4exp b).const_mul _)).const_mul _
    have hPval : ∫ z, (4 * ε * (M ^ 2 + s ^ 2 * z ^ 2) +
        Q * (M ^ 4 * Real.exp (b * |z|) + (s ^ 2) ^ 2 * (z ^ 4 * Real.exp (b * |z|)))) ∂(gaussianReal 0 1)
        = 4 * ε * (M ^ 2 + W) + Q * (M ^ 4 * I₀ + W ^ 2 * I₄) := by
      have iA : Integrable (fun z : ℝ => 4 * ε * (M ^ 2 + s ^ 2 * z ^ 2)) (gaussianReal 0 1) :=
        ((integrable_const _).add (integrable_z2.const_mul _)).const_mul _
      have iB1 : Integrable (fun z : ℝ => M ^ 4 * Real.exp (b * |z|)) (gaussianReal 0 1) :=
        (integrable_exp_abs b).const_mul _
      have iB2 : Integrable (fun z : ℝ => (s ^ 2) ^ 2 * (z ^ 4 * Real.exp (b * |z|))) (gaussianReal 0 1) :=
        (integrable_z4exp b).const_mul _
      rw [integral_add (f := fun z : ℝ => 4 * ε * (M ^ 2 + s ^ 2 * z ^ 2))
        (g := fun z : ℝ => Q * (M ^ 4 * Real.exp (b * |z|) +
          (s ^ 2) ^ 2 * (z ^ 4 * Real.exp (b * |z|)))) iA ((iB1.add iB2).const_mul _)]
      rw [integral_const_mul Q, integral_const_mul (4 * ε),
        integral_add (f := fun z : ℝ => M ^ 4 * Real.exp (b * |z|))
        (g := fun z : ℝ => (s ^ 2) ^ 2 * (z ^ 4 * Real.exp (b * |z|))) iB1 iB2,
        integral_const_mul (M ^ 4), integral_const_mul ((s ^ 2) ^ 2)]
      have hA : ∫ z, (M ^ 2 + s ^ 2 * z ^ 2) ∂(gaussianReal 0 1) = M ^ 2 + s ^ 2 := by
        have := int_quad (M ^ 2) 0 (s ^ 2); simpa using this
      rw [hA, hs2]
    have hbound : |∫ z, Rf F a (m h + s * z) (v h) ∂(gaussianReal 0 1)| ≤
        4 * ε * (M ^ 2 + W) + Q * (M ^ 4 * I₀ + W ^ 2 * I₄) := by
      rw [← hPval, ← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le hPint (ae_of_all _ hpt)
    have hMh : |M| < A₁ * h := by
      rw [abs_div, abs_of_pos hh, div_lt_iff₀ hh] at hA1; exact hA1
    have hWh : W < A₂ * h := by rw [div_lt_iff₀ hh] at hA2; exact hA2
    have key := estimate_arith ε' A₁ A₂ I₀ I₄ Q h M W hε' hA₁0 hA₂0 hI₀ hI₄ hQ hh
      (lt_of_lt_of_le hh1h (min_le_left _ _)) (lt_of_lt_of_le hh1h (min_le_right _ _))
      hMh hW0 hWh
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hh, div_lt_iff₀ hh]
    exact lt_of_le_of_lt hbound key
  -- the identity
  have hid2 : ∀ᶠ h in 𝓝[>] (0:ℝ),
      (∫ z, Rf F a (m h + √(w h) * z) (v h) ∂(gaussianReal 0 1)) / h + (F a (v h) - F a v₀) / h
      + dθ F a (v h) * ((m h - a) / h)
      + (1/2) * dθθ F a (v h) * ((m h - a) * ((m h - a) / h) + w h / h)
      = ((∫ z, F (m h + √(w h) * z) (v h) ∂(gaussianReal 0 1)) - F a v₀) / h := by
    filter_upwards [hpos, hM1, hw1] with h hh hM1h hw1h
    set M := m h - a with hMdef
    set W := w h with hWdef
    have hW0 : 0 ≤ W := hw0 h hh
    set s := √W with hsdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : s ≤ 1 := by
      have := Real.sqrt_le_sqrt hw1h; rwa [Real.sqrt_one] at this
    have hs2 : s ^ 2 = W := Real.sq_sqrt hW0
    obtain ⟨hvp, hvle⟩ := hvpos h hh
    have hcF : Continuous (fun z => F (m h + s * z) (v h)) :=
      (continuous_slice F hC hvp).comp (by fun_prop : Continuous fun z : ℝ => m h + s * z)
    have hRint : Integrable (fun z => Rf F a (m h + s * z) (v h)) (gaussianReal 0 1) := by
      refine ((integrable_exp_abs b).const_mul (K₀ * Real.exp b)).mono' ?_ (ae_of_all _ fun z => ?_)
      · unfold Rf
        exact (hcF.sub continuous_const |>.sub (by fun_prop) |>.sub (by fun_prop)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        have := hglob (m h + s * z) (v h) hvp hvle
        have e : m h + s * z - a = M + s * z := by rw [hMdef]; ring
        rw [e] at this
        have habs : |M + s * z| ≤ 1 + |z| := by
          calc |M + s * z| ≤ |M| + |s * z| := abs_add_le _ _
            _ = |M| + s * |z| := by rw [abs_mul, abs_of_nonneg hs0]
            _ ≤ 1 + |z| := by nlinarith [abs_nonneg z]
        have hexp : Real.exp (b * |M + s * z|) ≤ Real.exp b * Real.exp (b * |z|) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
        calc _ ≤ K₀ * Real.exp (b * |M + s * z|) := this
          _ ≤ K₀ * (Real.exp b * Real.exp (b * |z|)) := mul_le_mul_of_nonneg_left hexp hK₀
          _ = _ := by ring
    have hpt : (fun z => F (m h + s * z) (v h)) = fun z => Rf F a (m h + s * z) (v h) +
        ((F a (v h) + dθ F a (v h) * M + (1/2) * dθθ F a (v h) * M ^ 2)
          + (dθ F a (v h) * s + dθθ F a (v h) * M * s) * z
          + ((1/2) * dθθ F a (v h) * s ^ 2) * z ^ 2) := by
      funext z; unfold Rf; rw [hMdef]; ring
    have hInt : ∫ z, F (m h + s * z) (v h) ∂(gaussianReal 0 1) = (∫ z, Rf F a (m h + s * z) (v h) ∂(gaussianReal 0 1)) +
        ((F a (v h) + dθ F a (v h) * M + (1/2) * dθθ F a (v h) * M ^ 2)
          + ((1/2) * dθθ F a (v h) * s ^ 2)) := by
      rw [hpt, integral_add hRint (integrable_quad _ _ _), int_quad]
    rw [hInt, hs2]
    have := hh.ne'
    field_simp
    ring
  have hlim := (((hR.add hL1).add (((tendsto_dθ_a F hC (a := a) hv₀).comp hvt).mul hm)).add
    ((((tendsto_dθθ_a F hC (a := a) hv₀).comp hvt).const_mul (1/2)).mul ((hMt.mul hm).add hw)))
  have := hlim.congr' hid2
  convert this using 2
  ring


/-! ### Part 5: the Gaussian model -/

lemma std_repr (μ : ℝ) (W : ℝ≥0) (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ x, g x ∂gaussianReal μ W = ∫ z, g (μ + √(W:ℝ) * z) ∂(gaussianReal 0 1) := by
  have e : gaussianReal μ W =
      ((gaussianReal 0 1).map (fun z => √(W:ℝ) * z)).map (fun x => x + μ) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt W.2]
  rw [e, integral_map (by fun_prop) hg.aestronglyMeasurable,
    integral_map (φ := fun z => √(W:ℝ) * z) (f := fun x => g (x + μ)) (by fun_prop)
      (hg.comp (continuous_add_right μ)).aestronglyMeasurable]
  congr 1; funext z; rw [add_comm]

/-- mean of the Buyer's posterior mean at time `h` under the Seller's model -/
noncomputable def mF (p : Params) (h : ℝ) : ℝ :=
  p.buyerVar h * p.θ₀ / p.σ₀sq + (p.buyerVar h * h / p.σsq) * (p.θ₀ + p.μb)

/-- variance of the Buyer's posterior mean at time `h` under the Seller's model -/
noncomputable def wF (p : Params) (h : ℝ) : ℝ :=
  (p.buyerVar h * h / p.σsq) ^ 2 * p.σssq + (p.buyerVar h * √p.σsq / p.σsq) ^ 2 * h

lemma σssq_nonneg (p : Params) : 0 ≤ p.σssq := by
  unfold Params.σssq; have := p.σ₀sq_pos; have := p.σbsq_nonneg; linarith

lemma law_X (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hM : IsModel P (p.θ₀ + p.μb) p.σssq θ B) (h : ℝ) (hh : 0 ≤ h)
    (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ ω, g (p.buyerMean h (Y p.σsq θ B h.toNNReal ω)) ∂P =
      ∫ z, g (mF p h + √(wF p h) * z) ∂(gaussianReal 0 1) := by
  set hn := h.toNNReal
  have hhn : (hn : ℝ) = h := Real.coe_toNNReal _ hh
  set k := p.buyerVar h * h / p.σsq with hkdef
  set c := p.buyerVar h * √p.σsq / p.σsq with hcdef
  set α := p.buyerVar h * p.θ₀ / p.σ₀sq with hαdef
  have hX : (fun ω => p.buyerMean h (Y p.σsq θ B hn ω)) =
      fun ω => ((fun ω => k * θ ω) + (fun ω => c * B hn ω)) ω + α := by
    funext ω
    simp only [Params.buyerMean, postMean, Y, hhn, Pi.add_apply, k, c, α, Params.buyerVar]
    have := p.σ₀sq_pos.ne'; have := p.σsq_pos.ne'
    field_simp
    ring
  have h1 : P.map (fun ω => k * θ ω) =
      gaussianReal (k * (p.θ₀ + p.μb)) (⟨k ^ 2, sq_nonneg _⟩ * p.σssq.toNNReal) := by
    rw [show (fun ω => k * θ ω) = (fun x => k * x) ∘ θ from rfl,
      ← Measure.map_map (by fun_prop) hM.meas_θ, hM.law_θ]
    exact gaussianReal_map_const_mul k
  have h2 : P.map (fun ω => c * B hn ω) = gaussianReal (c * 0) (⟨c ^ 2, sq_nonneg _⟩ * hn) := by
    rw [show (fun ω => c * B hn ω) = (fun x => c * x) ∘ (B hn) from rfl,
      ← Measure.map_map (by fun_prop) (hM.meas_B hn), (hM.brownian.hasLaw_eval hn).map_eq]
    exact gaussianReal_map_const_mul c
  have hind : IndepFun (fun ω => k * θ ω) (fun ω => c * B hn ω) P :=
    hM.indep.comp (φ := fun x => k * x) (ψ := fun f : ℝ≥0 → ℝ => c * f hn)
      (by fun_prop)
      (show Measurable (fun f : ℝ≥0 → ℝ => c * f hn) by fun_prop)
  have h3 := gaussianReal_add_gaussianReal_of_indepFun hind h1 h2
  have hmeas : Measurable ((fun ω => k * θ ω) + (fun ω => c * B hn ω)) :=
    (hM.meas_θ.const_mul k).add ((hM.meas_B hn).const_mul c)
  have h4 : P.map (fun ω => p.buyerMean h (Y p.σsq θ B hn ω)) =
      gaussianReal (k * (p.θ₀ + p.μb) + c * 0 + α)
        (⟨k ^ 2, sq_nonneg _⟩ * p.σssq.toNNReal + ⟨c ^ 2, sq_nonneg _⟩ * hn) := by
    rw [hX, show (fun ω => ((fun ω => k * θ ω) + (fun ω => c * B hn ω)) ω + α) =
      (fun x => x + α) ∘ ((fun ω => k * θ ω) + (fun ω => c * B hn ω)) from rfl,
      ← Measure.map_map (by fun_prop) hmeas, h3, gaussianReal_map_add_const]
  have hXm : Measurable (fun ω => p.buyerMean h (Y p.σsq θ B hn ω)) := by
    rw [hX]; exact hmeas.add_const _
  rw [show (∫ ω, g (p.buyerMean h (Y p.σsq θ B hn ω)) ∂P) =
      ∫ x, g x ∂(P.map (fun ω => p.buyerMean h (Y p.σsq θ B hn ω))) from
      (integral_map hXm.aemeasurable hg.aestronglyMeasurable).symm, h4, std_repr _ _ g hg]
  have hmean : k * (p.θ₀ + p.μb) + c * 0 + α = mF p h := by
    unfold mF; rw [hkdef, hαdef]; ring
  have hvar : (((⟨k ^ 2, sq_nonneg _⟩ * p.σssq.toNNReal + ⟨c ^ 2, sq_nonneg _⟩ * hn : ℝ≥0)) : ℝ)
      = wF p h := by
    rw [NNReal.coe_add]
    unfold wF; rw [hkdef, hcdef]
    change (p.buyerVar h * h / p.σsq) ^ 2 * (p.σssq.toNNReal : ℝ) +
      (p.buyerVar h * √p.σsq / p.σsq) ^ 2 * (hn : ℝ) = _
    rw [hhn, Real.coe_toNNReal _ (σssq_nonneg p)]
  rw [hmean, hvar]

end FS4bAux

open FreeSamples.Revenue FS4bAux in
theorem solution (p : Params) (u : ℝ → ℝ → ℝ) (hu : HasMax u) (hA : Assumption1 u)
    (hG : GrowthPin (BR u) p.σ₀sq)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hM : IsModel P (p.θ₀ + p.μb) p.σssq θ B) :
    HasDerivWithinAt
      (fun h : ℝ => ∫ ω, BR u (p.buyerMean h (Y p.σsq θ B h.toNNReal ω)) (p.buyerVar h) ∂P)
      (drift (BR u) p.θ₀ p.σ₀sq p.μb * p.σ₀sq ^ 2 / p.σsq)
      (Set.Ici 0) 0 := by
  have hP := hM.isProb
  have h0 := p.σ₀sq_pos
  have hs := p.σsq_pos
  have hC := hA.2
  set f : ℝ → ℝ := fun h : ℝ => ∫ ω, BR u (p.buyerMean h (Y p.σsq θ B h.toNNReal ω))
    (p.buyerVar h) ∂P with hf
  have hv0 : p.buyerVar 0 = p.σ₀sq := by
    unfold Params.buyerVar postVar; simp [hs.ne']
  have hvpos : ∀ h > 0, 0 < p.buyerVar h ∧ p.buyerVar h ≤ p.σ₀sq := by
    intro h hh
    unfold Params.buyerVar postVar
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have := mul_pos (mul_pos h0 h0) hh; nlinarith
  have hf0 : f 0 = BR u p.θ₀ p.σ₀sq := by
    have hae : (fun ω => BR u (p.buyerMean 0 (Y p.σsq θ B (0:ℝ).toNNReal ω)) (p.buyerVar 0))
        =ᵐ[P] fun _ => BR u p.θ₀ p.σ₀sq := by
      filter_upwards [hM.brownian.eval_zero_ae_eq_zero] with ω hω
      have hY : Y p.σsq θ B (0:ℝ).toNNReal ω = 0 := by
        simp [Y, hω]
      rw [hY, hv0]
      congr 1
      unfold Params.buyerMean postMean
      rw [show postVar p.σsq p.σ₀sq 0 = p.σ₀sq from hv0]
      field_simp
      simp
    simp only [hf]
    rw [integral_congr_ae hae]
    simp
  -- derivative of the posterior variance
  have hvd : HasDerivAt (fun h => p.buyerVar h) (-(p.σ₀sq ^ 2 / p.σsq)) 0 := by
    unfold Params.buyerVar postVar
    have hden : HasDerivAt (fun h : ℝ => p.σ₀sq * h + p.σsq) p.σ₀sq 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_mul p.σ₀sq).add_const p.σsq
    have := (hasDerivAt_const (0:ℝ) (p.σ₀sq * p.σsq)).div hden (by simp [hs.ne'])
    refine this.congr_deriv ?_
    field_simp
    ring
  -- the slope limits for the mean and the variance
  have hm : Tendsto (fun h => (mF p h - p.θ₀) / h) (𝓝[>] 0) (𝓝 (p.σ₀sq * p.μb / p.σsq)) := by
    have hc : ContinuousAt (fun h : ℝ => p.σ₀sq * p.μb / (p.σ₀sq * h + p.σsq)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [hs.ne'])
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simp only [mul_zero, zero_add] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (0:ℝ) < h := hh
    unfold mF Params.buyerVar postVar
    field_simp
    ring
  have hw : Tendsto (fun h => wF p h / h) (𝓝[>] 0) (𝓝 (p.σ₀sq ^ 2 / p.σsq)) := by
    have hc : ContinuousAt (fun h : ℝ => (p.buyerVar h) ^ 2 * (h * p.σssq / p.σsq ^ 2 + 1 / p.σsq)) 0 :=
      (hvd.continuousAt.pow 2).mul (by fun_prop)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rw [hv0] at this
    simp only [zero_mul, zero_div, zero_add] at this
    convert this.congr' ?_ using 2
    · field_simp
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : (0:ℝ) < h := hh
      unfold wF
      simp only [div_pow, mul_pow, Real.sq_sqrt hs.le]
      field_simp
  have hw0 : ∀ h > 0, 0 ≤ wF p h := by
    intro h hh; unfold wF; have := σssq_nonneg p; positivity
  have key := keyA (BR u) hC p.θ₀ p.σ₀sq h0 hG (mF p) (wF p) (fun h => p.buyerVar h)
    _ _ _ hm hw hw0 hvd hv0 hvpos
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hIci : Set.Ici (0:ℝ) \ {0} = Set.Ioi 0 := by
    ext x; simp [lt_iff_le_and_ne, eq_comm]
  rw [hIci]
  convert key.congr' ?_ using 2
  · unfold drift; field_simp; ring
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (0:ℝ) < h := hh
    rw [slope_def_field, hf0, sub_zero]
    congr 1
    simp only [hf]
    have hl := law_X p P θ B hM h hh'.le (fun x => BR u x (p.buyerVar h))
      (continuous_slice (BR u) hC (hvpos h hh').1)
    rw [hl]

