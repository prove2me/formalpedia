-- Prove2me | solution 1 for BroughanRH.sbmArgument
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T02:09:30.925796+00:00
-- url     : https://prove2.me/submissions/e7e21f24-2ca8-497c-8a0a-c1d928312361
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Titchmarsh_logDeriv_riemannZeta_le_log_of_riemannHypothesis
import Theorems.Thm_riemann_hypothesis

section
open Complex MeasureTheory Filter Topology Set

namespace Contour

lemma integrable_one_add_abs_rpow {p : ℝ} (hp : 1 < p) :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-p)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := p) (by simpa using hp)
  simpa [Real.norm_eq_abs] using this

lemma re_line (R t : ℝ) : ((R : ℂ) + t * I).re = R := by simp
lemma im_line (R t : ℝ) : ((R : ℂ) + t * I).im = t := by simp

/-- Core vanishing lemma: a function holomorphic on a closed right half-plane, decaying like
`(1+|Re s|)^{-q} (1+|Im s|)^{-p}` with `p > 1`, `q > 0`, has zero integral over the boundary line. -/
theorem vline_eq_zero {Φ : ℂ → ℂ} {b C p q : ℝ} (hp : 1 < p) (hq : 0 < q)
    (hd : DifferentiableOn ℂ Φ {s : ℂ | b ≤ s.re})
    (hB : ∀ s : ℂ, b ≤ s.re → ‖Φ s‖ ≤ C * (1 + |s.re|) ^ (-q) * (1 + |s.im|) ^ (-p)) :
    ∫ t : ℝ, Φ (b + t * I) = 0 := by
  have hcont : ContinuousOn Φ {s : ℂ | b ≤ s.re} := hd.continuousOn
  have hC : 0 ≤ C := by
    have h1 := hB (b : ℂ) (by simp)
    have h2 : 0 < (1 + |((b : ℂ)).re|) ^ (-q) * (1 + |((b : ℂ)).im|) ^ (-p) := by positivity
    by_contra hneg
    push Not at hneg
    have : C * (1 + |((b : ℂ)).re|) ^ (-q) * (1 + |((b : ℂ)).im|) ^ (-p) < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (Φ b)]
  have hcl : ∀ R : ℝ, b ≤ R → Continuous (fun t : ℝ => Φ (R + t * I)) := by
    intro R hR
    refine hcont.comp_continuous (by fun_prop) (fun t => ?_)
    show b ≤ ((R : ℂ) + t * I).re
    rw [re_line]; exact hR
  have hptw : ∀ R : ℝ, b ≤ R → ∀ t : ℝ,
      ‖Φ (R + t * I)‖ ≤ C * (1 + |R|) ^ (-q) * (1 + |t|) ^ (-p) := by
    intro R hR t
    have := hB (R + t * I) (by rw [re_line]; exact hR)
    rwa [re_line, im_line] at this
  have hline : ∀ R : ℝ, b ≤ R → Integrable (fun t : ℝ => Φ (R + t * I)) := by
    intro R hR
    refine Integrable.mono' ((integrable_one_add_abs_rpow hp).const_mul (C * (1 + |R|) ^ (-q)))
      (hcl R hR).aestronglyMeasurable (Eventually.of_forall (fun t => ?_))
    simpa [mul_assoc] using hptw R hR t
  -- horizontal integrals vanish
  have hhor : ∀ R : ℝ, b ≤ R → ∀ c : ℝ,
      ‖∫ x : ℝ in b..R, Φ (x + c * I)‖ ≤ C * (1 + |c|) ^ (-p) * |R - b| := by
    intro R hR c
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    have hx' : b ≤ x := by
      rcases hx with ⟨h1, _⟩
      exact le_of_lt (lt_of_le_of_lt (le_min le_rfl hR) h1)
    have := hptw x hx' c
    have h1 : (1 + |x|) ^ (-q) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg x]) (by linarith)
    calc ‖Φ (x + c * I)‖ ≤ C * (1 + |x|) ^ (-q) * (1 + |c|) ^ (-p) := this
      _ ≤ C * 1 * (1 + |c|) ^ (-p) := by gcongr
      _ = C * (1 + |c|) ^ (-p) := by ring
  have htend : Tendsto (fun T : ℝ => (1 + |T|) ^ (-p)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => 1 + |T|) atTop atTop := by
      refine tendsto_atTop_add_const_left _ _ ?_
      exact tendsto_abs_atTop_atTop
    exact (tendsto_rpow_neg_atTop (by linarith)).comp h1
  have htend' : Tendsto (fun T : ℝ => (1 + |-T|) ^ (-p)) atTop (𝓝 0) := by
    simpa [abs_neg] using htend
  -- vertical integrals agree
  have hagree : ∀ R : ℝ, b ≤ R → ∫ t : ℝ, Φ (R + t * I) = ∫ t : ℝ, Φ (b + t * I) := by
    intro R hR
    have hrect : ∀ T : ℝ,
        (∫ x : ℝ in b..R, Φ (x + (-T) * I)) - (∫ x : ℝ in b..R, Φ (x + T * I)) +
        I • (∫ y : ℝ in (-T)..T, Φ (R + y * I)) - I • (∫ y : ℝ in (-T)..T, Φ (b + y * I)) = 0 := by
      intro T
      have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn Φ
        ((b : ℂ) + ((-T : ℝ) : ℂ) * I) ((R : ℂ) + (T : ℂ) * I) ?_
      · simpa [re_line, im_line] using this
      · refine hd.mono ?_
        intro s hs
        rw [mem_reProdIm, re_line, re_line] at hs
        have := hs.1
        rw [Set.mem_uIcc] at this
        show b ≤ s.re
        rcases this with h | h
        · exact h.1
        · linarith [h.1, h.2]
    have hA : Tendsto (fun T : ℝ => ∫ x : ℝ in b..R, Φ (x + (-T) * I)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (g := fun T : ℝ => C * (1 + |-T|) ^ (-p) * |R - b|)
        (fun _ => norm_nonneg _) (fun T => ?_) ?_
      · have := hhor R hR (-T); simpa using this
      · simpa using (htend'.const_mul C).mul_const |R - b|
    have hB' : Tendsto (fun T : ℝ => ∫ x : ℝ in b..R, Φ (x + T * I)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun T => hhor R hR T) ?_
      simpa using (htend.const_mul C).mul_const |R - b|
    have hV1 : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, Φ (R + y * I)) atTop
        (𝓝 (∫ t : ℝ, Φ (R + t * I))) :=
      MeasureTheory.intervalIntegral_tendsto_integral (hline R hR) tendsto_neg_atTop_atBot
        tendsto_id
    have hV2 : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, Φ (b + y * I)) atTop
        (𝓝 (∫ t : ℝ, Φ (b + t * I))) :=
      MeasureTheory.intervalIntegral_tendsto_integral (hline b le_rfl) tendsto_neg_atTop_atBot
        tendsto_id
    have hlim := ((hA.sub hB').add (hV1.const_smul I)).sub (hV2.const_smul I)
    have hlim0 : Tendsto (fun T : ℝ =>
        (∫ x : ℝ in b..R, Φ (x + (-T) * I)) - (∫ x : ℝ in b..R, Φ (x + T * I)) +
        I • (∫ y : ℝ in (-T)..T, Φ (R + y * I)) - I • (∫ y : ℝ in (-T)..T, Φ (b + y * I)))
        atTop (𝓝 0) := by
      simp only [hrect]; exact tendsto_const_nhds
    have heq := tendsto_nhds_unique hlim hlim0
    simp only [sub_zero, zero_add, smul_eq_mul] at heq
    have : I * ((∫ t : ℝ, Φ (R + t * I)) - ∫ t : ℝ, Φ (b + t * I)) = 0 := by
      rw [mul_sub]; exact heq
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h I_ne_zero
    · exact sub_eq_zero.mp h
  -- the right-hand vertical integrals tend to zero
  set K := ∫ t : ℝ, (1 + |t|) ^ (-p) with hK
  have hbound : ∀ R : ℝ, b ≤ R → ‖∫ t : ℝ, Φ (b + t * I)‖ ≤ C * (1 + |R|) ^ (-q) * K := by
    intro R hR
    rw [← hagree R hR]
    calc ‖∫ t : ℝ, Φ (R + t * I)‖ ≤ ∫ t : ℝ, C * (1 + |R|) ^ (-q) * (1 + |t|) ^ (-p) :=
          norm_integral_le_of_norm_le ((integrable_one_add_abs_rpow hp).const_mul _)
            (Eventually.of_forall (hptw R hR))
      _ = C * (1 + |R|) ^ (-q) * K := by rw [integral_const_mul]
  have hlimR : Tendsto (fun R : ℝ => C * (1 + |R|) ^ (-q) * K) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => 1 + |R|) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_abs_atTop_atTop
    have := ((tendsto_rpow_neg_atTop hq).comp h1).const_mul C
    simpa using this.mul_const K
  have : ‖∫ t : ℝ, Φ (b + t * I)‖ ≤ 0 :=
    ge_of_tendsto hlimR (eventually_atTop.2 ⟨b, fun R hR => hbound R hR⟩)
  exact norm_le_zero_iff.mp this

end Contour

end

section
open Complex MeasureTheory Filter Topology Set Real

namespace Contour

lemma pos_sq_add {α : ℝ} (hα : 0 < α) (τ : ℝ) : 0 < α ^ 2 + τ ^ 2 := by positivity

lemma integrable_inv_sq_add {α : ℝ} (hα : 0 < α) :
    Integrable (fun τ : ℝ => 1 / (α ^ 2 + τ ^ 2)) := by
  have h := (integrable_inv_one_add_sq.comp_div (R := α) hα.ne').const_mul (α ^ 2)⁻¹
  refine h.congr (Eventually.of_forall (fun τ => ?_))
  field_simp

lemma tendsto_div_sq_add_atTop {α : ℝ} (hα : 0 < α) :
    Tendsto (fun τ : ℝ => τ / (α ^ 2 + τ ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun τ : ℝ => τ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  refine squeeze_zero_norm' ?_ (by simpa using h1.norm)
  filter_upwards [eventually_gt_atTop 0] with τ hτ
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hτ, abs_of_pos (pos_sq_add hα τ),
    div_le_iff₀ (pos_sq_add hα τ)]
  rw [inv_mul_eq_div, le_div_iff₀ hτ]; nlinarith [sq_nonneg α]

lemma tendsto_div_sq_add_atBot {α : ℝ} (hα : 0 < α) :
    Tendsto (fun τ : ℝ => τ / (α ^ 2 + τ ^ 2)) atBot (𝓝 0) := by
  have := (tendsto_div_sq_add_atTop hα).comp tendsto_neg_atBot_atTop
  have h2 := this.neg
  simp only [neg_zero] at h2
  refine h2.congr (fun τ => ?_)
  simp [Function.comp, neg_div]

lemma hasDerivAt_arctan_div {α : ℝ} (hα : 0 < α) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.arctan (τ / α) / α) (1 / (α ^ 2 + τ ^ 2)) τ := by
  have h := ((hasDerivAt_id τ).div_const α).arctan
  refine (h.div_const α).congr_deriv ?_
  simp only [id]
  field_simp

lemma tendsto_arctan_div_atTop {α : ℝ} (hα : 0 < α) :
    Tendsto (fun τ : ℝ => Real.arctan (τ / α) / α) atTop (𝓝 (π / 2 / α)) := by
  have h1 : Tendsto (fun τ : ℝ => τ / α) atTop atTop := tendsto_id.atTop_div_const hα
  have h2 := (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp h1
  exact h2.div_const α

lemma tendsto_arctan_div_atBot {α : ℝ} (hα : 0 < α) :
    Tendsto (fun τ : ℝ => Real.arctan (τ / α) / α) atBot (𝓝 (-(π / 2) / α)) := by
  have h1 : Tendsto (fun τ : ℝ => τ / α) atBot atBot := tendsto_id.atBot_div_const hα
  have h2 := (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot).comp h1
  exact h2.div_const α

lemma integral_inv_sq_add {α : ℝ} (hα : 0 < α) :
    ∫ τ : ℝ, 1 / (α ^ 2 + τ ^ 2) = π / α := by
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_arctan_div hα) (integrable_inv_sq_add hα)
    (tendsto_arctan_div_atBot hα) (tendsto_arctan_div_atTop hα)]
  ring

lemma integrable_inv_sq_add_sq {α : ℝ} (hα : 0 < α) :
    Integrable (fun τ : ℝ => 1 / (α ^ 2 + τ ^ 2) ^ 2) := by
  refine ((integrable_inv_sq_add hα).const_mul (1 / α ^ 2)).mono'
    ((continuous_const.div (by fun_prop) (fun τ => (pow_pos (pos_sq_add hα τ) 2).ne')).aestronglyMeasurable)
    (Eventually.of_forall (fun τ => ?_))
  have hp := pos_sq_add hα τ
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [sq_nonneg τ, sq_nonneg α, mul_pos hα hα]

lemma integrable_odd_sq {α : ℝ} (hα : 0 < α) :
    Integrable (fun τ : ℝ => τ / (α ^ 2 + τ ^ 2) ^ 2) := by
  refine ((integrable_inv_sq_add hα).const_mul (1 / α)).mono'
    ((continuous_id.div (by fun_prop) (fun τ => (pow_pos (pos_sq_add hα τ) 2).ne')).aestronglyMeasurable)
    (Eventually.of_forall (fun τ => ?_))
  have hp := pos_sq_add hα τ
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < (α ^ 2 + τ ^ 2) ^ 2)]
  rw [div_le_iff₀ (by positivity)]
  field_simp
  have : |τ| * α ≤ α ^ 2 + τ ^ 2 := by
    nlinarith [sq_abs τ, sq_nonneg (|τ| - α), abs_nonneg τ]
  nlinarith [abs_nonneg τ]

lemma integrable_sq_div_sq {α : ℝ} (hα : 0 < α) :
    Integrable (fun τ : ℝ => τ ^ 2 / (α ^ 2 + τ ^ 2) ^ 2) := by
  refine (integrable_inv_sq_add hα).mono'
    (((continuous_pow 2).div (by fun_prop) (fun τ => (pow_pos (pos_sq_add hα τ) 2).ne')).aestronglyMeasurable)
    (Eventually.of_forall (fun τ => ?_))
  have hp := pos_sq_add hα τ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hp]
  nlinarith [sq_nonneg τ, sq_nonneg α, mul_pos hp hp]

lemma integral_odd_sq {α : ℝ} :
    ∫ τ : ℝ, τ / (α ^ 2 + τ ^ 2) ^ 2 = 0 := by
  have h := integral_neg_eq_self (fun τ : ℝ => τ / (α ^ 2 + τ ^ 2) ^ 2) volume
  have h2 : (∫ τ : ℝ, (-τ) / (α ^ 2 + (-τ) ^ 2) ^ 2) = -∫ τ : ℝ, τ / (α ^ 2 + τ ^ 2) ^ 2 := by
    rw [← integral_neg]; congr 1; funext τ; ring
  linarith

lemma hasDerivAt_aux2 {α : ℝ} (hα : 0 < α) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => τ / (2 * α ^ 2 * (α ^ 2 + τ ^ 2)) + Real.arctan (τ / α) / (2 * α ^ 3))
      (1 / (α ^ 2 + τ ^ 2) ^ 2) τ := by
  have hp := pos_sq_add hα τ
  have h1 : HasDerivAt (fun τ : ℝ => 2 * α ^ 2 * (α ^ 2 + τ ^ 2)) (2 * α ^ 2 * (2 * τ)) τ := by
    have := ((hasDerivAt_id τ).pow 2).const_add (α ^ 2)
    refine (this.const_mul (2 * α ^ 2)).congr_deriv ?_
    simp only [id]; ring
  have h2 := (hasDerivAt_id τ).div h1 (by positivity)
  have h3 := (((hasDerivAt_id τ).div_const α).arctan).div_const (2 * α ^ 3)
  refine (h2.add h3).congr_deriv ?_
  simp only [id]
  field_simp
  ring

lemma integral_inv_sq_add_sq {α : ℝ} (hα : 0 < α) :
    ∫ τ : ℝ, 1 / (α ^ 2 + τ ^ 2) ^ 2 = π / (2 * α ^ 3) := by
  have hbot : Tendsto (fun τ : ℝ => τ / (2 * α ^ 2 * (α ^ 2 + τ ^ 2)) +
      Real.arctan (τ / α) / (2 * α ^ 3)) atBot (𝓝 (0 / (2 * α ^ 2) + (-(π / 2)) / (2 * α ^ 3))) := by
    have e1 : (fun τ : ℝ => τ / (2 * α ^ 2 * (α ^ 2 + τ ^ 2))) =
        fun τ => τ / (α ^ 2 + τ ^ 2) / (2 * α ^ 2) := by funext τ; field_simp
    have e2 : (fun τ : ℝ => Real.arctan (τ / α) / (2 * α ^ 3)) =
        fun τ => Real.arctan (τ / α) / α / (2 * α ^ 2) := by funext τ; field_simp; try ring
    rw [show (fun τ : ℝ => τ / (2 * α ^ 2 * (α ^ 2 + τ ^ 2)) + Real.arctan (τ / α) / (2 * α ^ 3)) =
      fun τ => τ / (α ^ 2 + τ ^ 2) / (2 * α ^ 2) + Real.arctan (τ / α) / α / (2 * α ^ 2) by
        funext τ; rw [congrFun e1 τ, congrFun e2 τ]]
    have := ((tendsto_div_sq_add_atBot hα).div_const (2 * α ^ 2)).add
      ((tendsto_arctan_div_atBot hα).div_const (2 * α ^ 2))
    convert this using 2; field_simp; try ring
  have htop : Tendsto (fun τ : ℝ => τ / (2 * α ^ 2 * (α ^ 2 + τ ^ 2)) +
      Real.arctan (τ / α) / (2 * α ^ 3)) atTop (𝓝 (0 / (2 * α ^ 2) + (π / 2) / (2 * α ^ 3))) := by
    rw [show (fun τ : ℝ => τ / (2 * α ^ 2 * (α ^ 2 + τ ^ 2)) + Real.arctan (τ / α) / (2 * α ^ 3)) =
      fun τ => τ / (α ^ 2 + τ ^ 2) / (2 * α ^ 2) + Real.arctan (τ / α) / α / (2 * α ^ 2) by
        funext τ; field_simp; try ring]
    have := ((tendsto_div_sq_add_atTop hα).div_const (2 * α ^ 2)).add
      ((tendsto_arctan_div_atTop hα).div_const (2 * α ^ 2))
    convert this using 2; field_simp; try ring
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_aux2 hα) (integrable_inv_sq_add_sq hα)
    hbot htop]
  field_simp; try ring

lemma integral_sq_div_sq {α : ℝ} (hα : 0 < α) :
    ∫ τ : ℝ, τ ^ 2 / (α ^ 2 + τ ^ 2) ^ 2 = π / (2 * α) := by
  have e : (fun τ : ℝ => τ ^ 2 / (α ^ 2 + τ ^ 2) ^ 2) =
      fun τ => 1 / (α ^ 2 + τ ^ 2) - α ^ 2 * (1 / (α ^ 2 + τ ^ 2) ^ 2) := by
    funext τ; have := pos_sq_add hα τ; field_simp; try ring
  rw [e, integral_sub (integrable_inv_sq_add hα) ((integrable_inv_sq_add_sq hα).const_mul _),
    integral_const_mul, integral_inv_sq_add hα, integral_inv_sq_add_sq hα]
  field_simp; try ring

end Contour

end

section
open Complex MeasureTheory Filter Topology Set

namespace Contour

lemma norm_sub_ge {s c : ℂ} {m : ℝ} (hm : 0 < m) (h : m ≤ ‖s - c‖) :
    (1 + ‖s‖) / (1 + (1 + ‖c‖) / m) ≤ ‖s - c‖ := by
  rw [div_le_iff₀ (by positivity)]
  have h1 : ‖s‖ - ‖c‖ ≤ ‖s - c‖ := norm_sub_norm_le s c
  have h2 : (1 + ‖c‖) ≤ (1 + ‖c‖) / m * ‖s - c‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]; nlinarith [norm_nonneg c]
  nlinarith

lemma one_add_norm_rpow_le {s : ℂ} {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) :
    (1 + ‖s‖) ^ (-(q + p)) ≤ (1 + |s.re|) ^ (-q) * (1 + |s.im|) ^ (-p) := by
  rw [neg_add, Real.rpow_add (by positivity)]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [Complex.abs_re_le_norm s])
      (by linarith)
  · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [Complex.abs_im_le_norm s])
      (by linarith)

/-- Vanishing of the line integral under a bound `C (1+‖s‖)^{-e}`, `e > 1`, valid for large `‖s‖`. -/
theorem vline_of_bound {Φ : ℂ → ℂ} {b R0 C e : ℝ} (he : 1 < e)
    (hd : DifferentiableOn ℂ Φ {s : ℂ | b ≤ s.re})
    (hB : ∀ s : ℂ, b ≤ s.re → R0 ≤ ‖s‖ → ‖Φ s‖ ≤ C * (1 + ‖s‖) ^ (-e)) :
    Integrable (fun t : ℝ => Φ (b + t * I)) ∧ ∫ t : ℝ, Φ (b + t * I) = 0 := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ s ∈ {s : ℂ | b ≤ s.re} ∩ Metric.closedBall 0 R0, ‖Φ s‖ ≤ M := by
    have hK : IsCompact ({s : ℂ | b ≤ s.re} ∩ Metric.closedBall 0 R0) :=
      (isCompact_closedBall 0 R0).inter_left (isClosed_le continuous_const Complex.continuous_re)
    exact hK.exists_bound_of_continuousOn (hd.continuousOn.mono inter_subset_left)
  set C' := max C (max M 0 * (1 + |R0|) ^ e) with hC'
  have hC'0 : 0 ≤ C' := le_trans (by positivity) (le_max_right _ _)
  have hglob : ∀ s : ℂ, b ≤ s.re → ‖Φ s‖ ≤ C' * (1 + ‖s‖) ^ (-e) := by
    intro s hs
    by_cases hR : R0 ≤ ‖s‖
    · calc ‖Φ s‖ ≤ C * (1 + ‖s‖) ^ (-e) := hB s hs hR
        _ ≤ C' * (1 + ‖s‖) ^ (-e) := by gcongr; exact le_max_left _ _
    · push Not at hR
      have hmem : s ∈ {s : ℂ | b ≤ s.re} ∩ Metric.closedBall 0 R0 :=
        ⟨hs, by simpa using hR.le⟩
      have h1 := hM s hmem
      have h2 : (1 + |R0|) ^ (-e) ≤ (1 + ‖s‖) ^ (-e) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [le_abs_self R0])
          (by linarith)
      have h3 : (1 + |R0|) ^ e * (1 + |R0|) ^ (-e) = 1 := by
        rw [← Real.rpow_add (by positivity)]; simp
      calc ‖Φ s‖ ≤ max M 0 := h1.trans (le_max_left _ _)
        _ = max M 0 * (1 + |R0|) ^ e * (1 + |R0|) ^ (-e) := by rw [mul_assoc, h3, mul_one]
        _ ≤ C' * (1 + ‖s‖) ^ (-e) :=
          mul_le_mul (le_max_right _ _) h2 (by positivity) hC'0
  constructor
  · have hc : Continuous (fun t : ℝ => Φ (b + t * I)) := by
      refine hd.continuousOn.comp_continuous (by fun_prop) (fun t => ?_)
      show b ≤ ((b : ℂ) + t * I).re
      rw [re_line]
    refine Integrable.mono' ((integrable_one_add_abs_rpow he).const_mul C')
      hc.aestronglyMeasurable (Eventually.of_forall (fun t => ?_))
    have h1 := hglob (b + t * I) (by rw [re_line])
    have h2 : (1 + ‖(b : ℂ) + t * I‖) ^ (-e) ≤ (1 + |t|) ^ (-e) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      have := Complex.abs_im_le_norm ((b : ℂ) + t * I)
      rw [im_line] at this; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC'0)
  · refine vline_eq_zero (C := C') (p := (e + 1) / 2) (q := (e - 1) / 2) (by linarith)
      (by linarith) hd (fun s hs => ?_)
    have h1 := hglob s hs
    have h2 := one_add_norm_rpow_le (s := s) (q := (e - 1) / 2) (p := (e + 1) / 2)
      (by linarith) (by linarith)
    have h3 : (e - 1) / 2 + (e + 1) / 2 = e := by ring
    rw [h3] at h2
    calc ‖Φ s‖ ≤ C' * (1 + ‖s‖) ^ (-e) := h1
      _ ≤ C' * ((1 + |s.re|) ^ (-((e - 1) / 2)) * (1 + |s.im|) ^ (-((e + 1) / 2))) :=
          mul_le_mul_of_nonneg_left h2 hC'0
      _ = _ := by ring

lemma integrable_shift_inv {α y : ℝ} (hα : 0 < α) :
    Integrable (fun t : ℝ => 1 / (α ^ 2 + (t - y) ^ 2)) :=
  (integrable_inv_sq_add hα).comp_sub_right y

lemma integral_shift_inv {α y : ℝ} (hα : 0 < α) :
    ∫ t : ℝ, 1 / (α ^ 2 + (t - y) ^ 2) = Real.pi / α := by
  rw [integral_sub_right_eq_self (fun τ => 1 / (α ^ 2 + τ ^ 2)) y]
  exact integral_inv_sq_add hα

/-- Poisson integral formula for a right half-plane, for holomorphic functions of sublinear growth. -/
theorem poisson {F : ℂ → ℂ} {b C r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hd : DifferentiableOn ℂ F {s : ℂ | b ≤ s.re})
    (hB : ∀ s : ℂ, b ≤ s.re → ‖F s‖ ≤ C * (1 + ‖s‖) ^ r) {α y : ℝ} (hα : 0 < α) :
    Integrable (fun t : ℝ => F (b + t * I) / (((α ^ 2 + (t - y) ^ 2 : ℝ)) : ℂ)) ∧
    ∫ t : ℝ, F (b + t * I) / (((α ^ 2 + (t - y) ^ 2 : ℝ)) : ℂ) =
      ((Real.pi / α : ℝ) : ℂ) * F (((b + α : ℝ) : ℂ) + y * I) := by
  set z : ℂ := ((b + α : ℝ) : ℂ) + y * I with hz
  set zs : ℂ := ((b - α : ℝ) : ℂ) + y * I with hzs
  have hzre : z.re = b + α := by simp [z]
  have hzsre : zs.re = b - α := by simp [zs]
  have hnhds : {s : ℂ | b ≤ s.re} ∈ 𝓝 z := by
    apply mem_of_superset ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show b < z.re by rw [hzre]; linarith))
    intro s hs; exact le_of_lt (show b < s.re from hs)
  have hne : ∀ s : ℂ, b ≤ s.re → s - zs ≠ 0 := by
    intro s hs h
    have : (s - zs).re = 0 := by rw [h]; simp
    rw [sub_re, hzsre] at this; linarith
  have hC : 0 ≤ C := by
    have h1 := hB z (by rw [hzre]; linarith)
    by_contra hneg; push Not at hneg
    have : C * (1 + ‖z‖) ^ r < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith [norm_nonneg (F z)]
  set Φ : ℂ → ℂ := fun s => dslope F z s - (F s - F z) / (s - zs) with hΦ
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | b ≤ s.re} := by
    refine ((differentiableOn_dslope hnhds).2 hd).sub ?_
    exact (hd.sub_const _).div (differentiableOn_id.sub_const _) hne
  -- formula off `z`
  have hΦform : ∀ s : ℂ, b ≤ s.re → s ≠ z →
      Φ s = (F s - F z) * (z - zs) / ((s - z) * (s - zs)) := by
    intro s hs hsz
    have h1 : s - z ≠ 0 := sub_ne_zero.2 hsz
    have h2 := hne s hs
    simp only [hΦ, dslope_of_ne _ hsz, slope_def_field]
    field_simp
    ring
  -- decay bound
  have hdec : ∀ s : ℂ, b ≤ s.re → ‖z‖ + 1 ≤ ‖s‖ →
      ‖Φ s‖ ≤ ((C + ‖F z‖) * ‖z - zs‖ * (1 + (1 + ‖z‖) / 1) * (1 + (1 + ‖zs‖) / α)) *
        (1 + ‖s‖) ^ (-(2 - r)) := by
    intro s hs hsn
    have hsz1 : 1 ≤ ‖s - z‖ := by
      have := norm_sub_norm_le s z; linarith
    have hsz : s ≠ z := by
      intro h; rw [h, sub_self, norm_zero] at hsz1; linarith
    have hszs : α ≤ ‖s - zs‖ := by
      have h1 : (s - zs).re ≤ ‖s - zs‖ := Complex.re_le_norm _
      rw [sub_re, hzsre] at h1; linarith
    have l1 := norm_sub_ge (s := s) (c := z) one_pos hsz1
    have l2 := norm_sub_ge (s := s) (c := zs) hα hszs
    set k1 := 1 + (1 + ‖z‖) / 1
    set k2 := 1 + (1 + ‖zs‖) / α
    have hk1 : 0 < k1 := by positivity
    have hk2 : 0 < k2 := by positivity
    have hS : 0 < 1 + ‖s‖ := by positivity
    have hFs : ‖F s - F z‖ ≤ (C + ‖F z‖) * (1 + ‖s‖) ^ r := by
      have h1 := hB s hs
      have h2 : 1 ≤ (1 + ‖s‖) ^ r := Real.one_le_rpow (by linarith [norm_nonneg s]) hr0
      calc ‖F s - F z‖ ≤ ‖F s‖ + ‖F z‖ := norm_sub_le _ _
        _ ≤ C * (1 + ‖s‖) ^ r + ‖F z‖ * (1 + ‖s‖) ^ r := by
          gcongr; nlinarith [norm_nonneg (F z)]
        _ = _ := by ring
    rw [hΦform s hs hsz, norm_div, norm_mul, norm_mul]
    have hden : (1 + ‖s‖) / k1 * ((1 + ‖s‖) / k2) ≤ ‖s - z‖ * ‖s - zs‖ :=
      mul_le_mul l1 l2 (by positivity) (norm_nonneg _)
    have hpos : 0 < (1 + ‖s‖) / k1 * ((1 + ‖s‖) / k2) := by positivity
    rw [div_le_iff₀ (lt_of_lt_of_le hpos hden)]
    have hrp : (1 + ‖s‖) ^ (-(2 - r)) * ((1 + ‖s‖) * (1 + ‖s‖)) = (1 + ‖s‖) ^ r := by
      rw [show (1 + ‖s‖) * (1 + ‖s‖) = (1 + ‖s‖) ^ (2 : ℝ) by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring,
        ← Real.rpow_add hS]
      ring_nf
    calc ‖F s - F z‖ * ‖z - zs‖ ≤ (C + ‖F z‖) * (1 + ‖s‖) ^ r * ‖z - zs‖ := by
          gcongr
      _ = ((C + ‖F z‖) * ‖z - zs‖ * k1 * k2) * (1 + ‖s‖) ^ (-(2 - r)) *
            ((1 + ‖s‖) / k1 * ((1 + ‖s‖) / k2)) := by
          rw [← hrp]; field_simp
      _ ≤ ((C + ‖F z‖) * ‖z - zs‖ * k1 * k2) * (1 + ‖s‖) ^ (-(2 - r)) *
            (‖s - z‖ * ‖s - zs‖) := by gcongr
  obtain ⟨hΦint, hΦ0⟩ := vline_of_bound (by linarith : 1 < 2 - r) hΦd hdec
  -- the kernel on the line
  have hline : ∀ t : ℝ, Φ (b + t * I) =
      (F (b + t * I) - F z) * (((-(2 * α) / (α ^ 2 + (t - y) ^ 2) : ℝ)) : ℂ) := by
    intro t
    have hs : b ≤ ((b : ℂ) + t * I).re := by rw [re_line]
    have hsz : (b : ℂ) + t * I ≠ z := by
      intro h; have := congrArg Complex.re h; rw [re_line, hzre] at this; linarith
    rw [hΦform _ hs hsz]
    have hP : ((b : ℂ) + t * I - z) * ((b : ℂ) + t * I - zs) =
        -(((α ^ 2 + (t - y) ^ 2 : ℝ)) : ℂ) := by
      simp only [hz, hzs]; push_cast
      linear_combination ((t : ℂ) - y) ^ 2 * I_sq
    have hzz : z - zs = ((2 * α : ℝ) : ℂ) := by simp only [hz, hzs]; push_cast; ring
    have hpos : (((α ^ 2 + (t - y) ^ 2 : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast (pos_sq_add hα (t - y)).ne'
    rw [hP, hzz]
    push_cast
    field_simp
  have hkr_eq : (fun t : ℝ => -(2 * α) / (α ^ 2 + (t - y) ^ 2)) =
      fun t => -(2 * α) * (1 / (α ^ 2 + (t - y) ^ 2)) := by funext t; ring
  have hkr : Integrable (fun t : ℝ => -(2 * α) / (α ^ 2 + (t - y) ^ 2)) := by
    rw [hkr_eq]; exact (integrable_shift_inv hα).const_mul _
  have hkrval : ∫ t : ℝ, -(2 * α) / (α ^ 2 + (t - y) ^ 2) = -(2 * Real.pi) := by
    rw [hkr_eq, integral_const_mul, integral_shift_inv hα]; field_simp
  set k : ℝ → ℂ := fun t => (((-(2 * α) / (α ^ 2 + (t - y) ^ 2) : ℝ)) : ℂ) with hk
  have hkint : Integrable k := hkr.ofReal
  have hkval : ∫ t : ℝ, k t = ((-(2 * Real.pi) : ℝ) : ℂ) := by
    rw [← hkrval]; exact integral_ofReal
  have hfun : (fun t : ℝ => F (b + t * I) / (((α ^ 2 + (t - y) ^ 2 : ℝ)) : ℂ)) =
      fun t : ℝ => (((-(2 * α))⁻¹ : ℝ) : ℂ) * (Φ (b + t * I) + F z * k t) := by
    funext t
    rw [hline t]
    simp only [hk]
    have hpos : (((α ^ 2 + (t - y) ^ 2 : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast (pos_sq_add hα (t - y)).ne'
    have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
    push_cast
    field_simp
    ring
  rw [hfun]
  refine ⟨(hΦint.add (hkint.const_mul (F z))).const_mul _, ?_⟩
  rw [integral_const_mul, integral_add hΦint (hkint.const_mul (F z)), integral_const_mul, hΦ0,
    hkval]
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  push_cast
  field_simp
  ring

lemma integrable_shift_odd {α y : ℝ} (hα : 0 < α) :
    Integrable (fun t : ℝ => (t - y) / (α ^ 2 + (t - y) ^ 2) ^ 2) :=
  (integrable_odd_sq hα).comp_sub_right y

lemma integral_shift_odd {α y : ℝ} :
    ∫ t : ℝ, (t - y) / (α ^ 2 + (t - y) ^ 2) ^ 2 = 0 := by
  rw [integral_sub_right_eq_self (fun τ => τ / (α ^ 2 + τ ^ 2) ^ 2) y]
  exact integral_odd_sq

lemma integrable_shift_sq {α y : ℝ} (hα : 0 < α) :
    Integrable (fun t : ℝ => (t - y) ^ 2 / (α ^ 2 + (t - y) ^ 2) ^ 2) :=
  (integrable_sq_div_sq hα).comp_sub_right y

lemma integral_shift_sq {α y : ℝ} (hα : 0 < α) :
    ∫ t : ℝ, (t - y) ^ 2 / (α ^ 2 + (t - y) ^ 2) ^ 2 = Real.pi / (2 * α) := by
  rw [integral_sub_right_eq_self (fun τ => τ ^ 2 / (α ^ 2 + τ ^ 2) ^ 2) y]
  exact integral_sq_div_sq hα

/-- Derivative form of the Poisson formula. -/
theorem poisson_deriv {F : ℂ → ℂ} {b C r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hd : DifferentiableOn ℂ F {s : ℂ | b ≤ s.re})
    (hB : ∀ s : ℂ, b ≤ s.re → ‖F s‖ ≤ C * (1 + ‖s‖) ^ r) {α y : ℝ} (hα : 0 < α) :
    Integrable (fun t : ℝ => F (b + t * I) * ((((t - y) / (α ^ 2 + (t - y) ^ 2) ^ 2 : ℝ)) : ℂ)) ∧
    ∫ t : ℝ, F (b + t * I) * ((((t - y) / (α ^ 2 + (t - y) ^ 2) ^ 2 : ℝ)) : ℂ) =
      (I * ((Real.pi / (2 * α) : ℝ) : ℂ)) * deriv F (((b + α : ℝ) : ℂ) + y * I) := by
  set z : ℂ := ((b + α : ℝ) : ℂ) + y * I with hz
  set zs : ℂ := ((b - α : ℝ) : ℂ) + y * I with hzs
  have hzre : z.re = b + α := by simp [z]
  have hzsre : zs.re = b - α := by simp [zs]
  have hnhds : {s : ℂ | b ≤ s.re} ∈ 𝓝 z := by
    apply mem_of_superset ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show b < z.re by rw [hzre]; linarith))
    intro s hs; exact le_of_lt (show b < s.re from hs)
  have hne : ∀ s : ℂ, b ≤ s.re → s - zs ≠ 0 := by
    intro s hs h
    have : (s - zs).re = 0 := by rw [h]; simp
    rw [sub_re, hzsre] at this; linarith
  have hC : 0 ≤ C := by
    have h1 := hB z (by rw [hzre]; linarith)
    by_contra hneg; push Not at hneg
    have : C * (1 + ‖z‖) ^ r < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith [norm_nonneg (F z)]
  set D := deriv F z with hD
  set N : ℂ → ℂ := fun s => F s - F z - D * (s - z) with hN
  set Φ : ℂ → ℂ := fun s => dslope (dslope F z) z s - N s / (s - zs) ^ 2 with hΦ
  have hD1 : DifferentiableOn ℂ (dslope F z) {s : ℂ | b ≤ s.re} := (differentiableOn_dslope hnhds).2 hd
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | b ≤ s.re} := by
    refine ((differentiableOn_dslope hnhds).2 hD1).sub ?_
    refine DifferentiableOn.div ?_ ((differentiableOn_id.sub_const _).pow 2)
      (fun s hs => pow_ne_zero 2 (hne s hs))
    exact ((hd.sub_const _).sub ((differentiableOn_id.sub_const _).const_mul _))
  have hΦform : ∀ s : ℂ, b ≤ s.re → s ≠ z →
      Φ s = N s * (1 / (s - z) ^ 2 - 1 / (s - zs) ^ 2) := by
    intro s hs hsz
    have h1 : s - z ≠ 0 := sub_ne_zero.2 hsz
    have h2 := hne s hs
    simp only [hΦ, hN, dslope_of_ne _ hsz, slope_def_field, dslope_same]
    rw [← hD]
    field_simp
  have hdec : ∀ s : ℂ, b ≤ s.re → ‖z‖ + 1 ≤ ‖s‖ →
      ‖Φ s‖ ≤ (((C + ‖F z‖ + ‖D‖ * (1 + ‖z‖)) * (‖z - zs‖ * (2 + ‖z‖ + ‖zs‖))) *
        ((1 + (1 + ‖z‖) / 1) * (1 + (1 + ‖zs‖) / α)) ^ 2) * (1 + ‖s‖) ^ (-(2 : ℝ)) := by
    intro s hs hsn
    have hsz1 : 1 ≤ ‖s - z‖ := by
      have := norm_sub_norm_le s z; linarith
    have hsz : s ≠ z := by
      intro h; rw [h, sub_self, norm_zero] at hsz1; linarith
    have hszs : α ≤ ‖s - zs‖ := by
      have h1 : (s - zs).re ≤ ‖s - zs‖ := Complex.re_le_norm _
      rw [sub_re, hzsre] at h1; linarith
    have l1 := norm_sub_ge (s := s) (c := z) one_pos hsz1
    have l2 := norm_sub_ge (s := s) (c := zs) hα hszs
    set k1 := 1 + (1 + ‖z‖) / 1
    set k2 := 1 + (1 + ‖zs‖) / α
    have hk1 : 0 < k1 := by positivity
    have hk2 : 0 < k2 := by positivity
    set S := 1 + ‖s‖ with hSdef
    have hS : 0 < S := by positivity
    have h1z : s - z ≠ 0 := sub_ne_zero.2 hsz
    have h2z := hne s hs
    have hNb : ‖N s‖ ≤ (C + ‖F z‖ + ‖D‖ * (1 + ‖z‖)) * S := by
      have h1 := hB s hs
      have h2 : (1 + ‖s‖) ^ r ≤ S := by
        have := Real.rpow_le_rpow_of_exponent_le (x := 1 + ‖s‖) (by linarith [norm_nonneg s])
          (le_of_lt hr)
        simpa using this
      have h3 : ‖s - z‖ ≤ (1 + ‖z‖) * S := by
        have := norm_sub_le s z
        nlinarith [norm_nonneg s, norm_nonneg z]
      have h4 : 1 ≤ S := by linarith [norm_nonneg s]
      calc ‖N s‖ ≤ ‖F s‖ + ‖F z‖ + ‖D‖ * ‖s - z‖ := by
            simp only [hN]
            calc ‖F s - F z - D * (s - z)‖ ≤ ‖F s - F z‖ + ‖D * (s - z)‖ := norm_sub_le _ _
              _ ≤ ‖F s‖ + ‖F z‖ + ‖D * (s - z)‖ := by gcongr; exact norm_sub_le _ _
              _ = _ := by rw [norm_mul]
        _ ≤ C * S + ‖F z‖ * S + ‖D‖ * ((1 + ‖z‖) * S) := by
            gcongr
            · exact h1.trans (mul_le_mul_of_nonneg_left h2 hC)
            · nlinarith [norm_nonneg (F z)]
        _ = _ := by ring
    have hKb : ‖1 / (s - z) ^ 2 - 1 / (s - zs) ^ 2‖ ≤
        (‖z - zs‖ * (2 + ‖z‖ + ‖zs‖)) * S / ((S / k1) * (S / k2)) ^ 2 := by
      have heq : 1 / (s - z) ^ 2 - 1 / (s - zs) ^ 2 =
          (z - zs) * (2 * s - z - zs) / ((s - z) * (s - zs)) ^ 2 := by
        field_simp; ring
      rw [heq, norm_div, norm_mul, norm_pow, norm_mul]
      have hnum : ‖2 * s - z - zs‖ ≤ (2 + ‖z‖ + ‖zs‖) * S := by
        have : ‖2 * s - z - zs‖ ≤ 2 * ‖s‖ + ‖z‖ + ‖zs‖ := by
          calc ‖2 * s - z - zs‖ ≤ ‖2 * s - z‖ + ‖zs‖ := norm_sub_le _ _
            _ ≤ ‖2 * s‖ + ‖z‖ + ‖zs‖ := by gcongr; exact norm_sub_le _ _
            _ = 2 * ‖s‖ + ‖z‖ + ‖zs‖ := by rw [norm_mul]; norm_num
        nlinarith [norm_nonneg s, norm_nonneg z, norm_nonneg zs]
      have hden : (S / k1) * (S / k2) ≤ ‖s - z‖ * ‖s - zs‖ :=
        mul_le_mul l1 l2 (by positivity) (norm_nonneg _)
      have hpos : 0 < (S / k1) * (S / k2) := by positivity
      calc ‖z - zs‖ * ‖2 * s - z - zs‖ / (‖s - z‖ * ‖s - zs‖) ^ 2
          ≤ ‖z - zs‖ * ((2 + ‖z‖ + ‖zs‖) * S) / ((S / k1) * (S / k2)) ^ 2 := by
            gcongr
        _ = _ := by ring
    rw [hΦform s hs hsz, norm_mul]
    have hrp : S ^ (-(2 : ℝ)) * S ^ 2 = 1 := by
      rw [show S ^ 2 = S ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hS]; simp
    calc ‖N s‖ * ‖1 / (s - z) ^ 2 - 1 / (s - zs) ^ 2‖
        ≤ ((C + ‖F z‖ + ‖D‖ * (1 + ‖z‖)) * S) *
          ((‖z - zs‖ * (2 + ‖z‖ + ‖zs‖)) * S / ((S / k1) * (S / k2)) ^ 2) :=
          mul_le_mul hNb hKb (norm_nonneg _) (by positivity)
      _ = (((C + ‖F z‖ + ‖D‖ * (1 + ‖z‖)) * (‖z - zs‖ * (2 + ‖z‖ + ‖zs‖))) *
            (k1 * k2) ^ 2) * (S ^ (-(2 : ℝ)) * S ^ 2) / S ^ 2 := by
          rw [hrp]; field_simp
      _ = (((C + ‖F z‖ + ‖D‖ * (1 + ‖z‖)) * (‖z - zs‖ * (2 + ‖z‖ + ‖zs‖))) *
            (k1 * k2) ^ 2) * S ^ (-(2 : ℝ)) := by
          field_simp
  obtain ⟨hΦint, hΦ0⟩ := vline_of_bound (by norm_num : (1 : ℝ) < 2) hΦd hdec
  -- kernels on the line
  set o : ℝ → ℝ := fun t => (t - y) / (α ^ 2 + (t - y) ^ 2) ^ 2 with ho
  set q : ℝ → ℝ := fun t => (t - y) ^ 2 / (α ^ 2 + (t - y) ^ 2) ^ 2 with hq
  have hlineK : ∀ t : ℝ, 1 / ((b : ℂ) + t * I - z) ^ 2 - 1 / ((b : ℂ) + t * I - zs) ^ 2 =
      ((4 * α : ℝ) : ℂ) * I * ((o t : ℝ) : ℂ) := by
    intro t
    have hP := pos_sq_add hα (t - y)
    have hA : (b : ℂ) + t * I - z = ((-α : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I := by
      simp only [hz]; push_cast; ring
    have hB2 : (b : ℂ) + t * I - zs = ((α : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I := by
      simp only [hzs]; push_cast; ring
    have hAB : (((-α : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I) * (((α : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I)
        = -(((α ^ 2 + (t - y) ^ 2 : ℝ)) : ℂ) := by
      push_cast; linear_combination ((t : ℂ) - y) ^ 2 * I_sq
    have hA0 : ((-α : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hB0 : ((α : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hP0 : (((α ^ 2 + (t - y) ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    rw [hA, hB2, div_sub_div _ _ (pow_ne_zero 2 hA0) (pow_ne_zero 2 hB0), ← mul_pow, hAB]
    simp only [ho]
    push_cast
    field_simp
    ring
  have hlineK2 : ∀ t : ℝ, ((b : ℂ) + t * I - z) *
      (1 / ((b : ℂ) + t * I - z) ^ 2 - 1 / ((b : ℂ) + t * I - zs) ^ 2) =
      ((-(4 * α) : ℝ) : ℂ) * ((q t : ℝ) : ℂ) + ((-(4 * α ^ 2) : ℝ) : ℂ) * I * ((o t : ℝ) : ℂ) := by
    intro t
    have hA : (b : ℂ) + t * I - z = ((-α : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I := by
      simp only [hz]; push_cast; ring
    rw [hlineK t, hA]
    simp only [ho, hq, div_eq_mul_inv]
    push_cast
    linear_combination (4 * (α : ℂ) * ((t : ℂ) - y) ^ 2 *
      (((α : ℂ) ^ 2 + ((t : ℂ) - y) ^ 2) ^ 2)⁻¹) * I_sq
  have hΦline : ∀ t : ℝ, Φ (b + t * I) = N (b + t * I) * (((4 * α : ℝ) : ℂ) * I * ((o t : ℝ) : ℂ)) := by
    intro t
    have hs : b ≤ ((b : ℂ) + t * I).re := by rw [re_line]
    have hsz : (b : ℂ) + t * I ≠ z := by
      intro h; have := congrArg Complex.re h; rw [re_line, hzre] at this; linarith
    rw [hΦform _ hs hsz, hlineK t]
  have hoint : Integrable (fun t : ℝ => ((o t : ℝ) : ℂ)) := (integrable_shift_odd hα).ofReal
  have hqint : Integrable (fun t : ℝ => ((q t : ℝ) : ℂ)) := (integrable_shift_sq hα).ofReal
  have hoval : ∫ t : ℝ, ((o t : ℝ) : ℂ) = 0 := by
    rw [show (∫ t : ℝ, ((o t : ℝ) : ℂ)) = ((∫ t : ℝ, o t : ℝ) : ℂ) from integral_ofReal]
    simp only [ho]; rw [integral_shift_odd]; simp
  have hqval : ∫ t : ℝ, ((q t : ℝ) : ℂ) = ((Real.pi / (2 * α) : ℝ) : ℂ) := by
    rw [show (∫ t : ℝ, ((q t : ℝ) : ℂ)) = ((∫ t : ℝ, q t : ℝ) : ℂ) from integral_ofReal]
    simp only [hq]; rw [integral_shift_sq hα]
  have hfun : (fun t : ℝ => F (b + t * I) * ((((t - y) / (α ^ 2 + (t - y) ^ 2) ^ 2 : ℝ)) : ℂ)) =
      fun t : ℝ => (((4 * α : ℝ) : ℂ) * I)⁻¹ * (Φ (b + t * I) +
        F z * (((4 * α : ℝ) : ℂ) * I * ((o t : ℝ) : ℂ)) +
        D * (((-(4 * α) : ℝ) : ℂ) * ((q t : ℝ) : ℂ) + ((-(4 * α ^ 2) : ℝ) : ℂ) * I * ((o t : ℝ) : ℂ))) := by
    funext t
    change F (b + t * I) * ((o t : ℝ) : ℂ) = _
    rw [hΦline t, ← hlineK2 t, hlineK t]
    have h4' : ((4 * α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (4 * α) ≠ 0)
    have h4 : (((4 * α : ℝ) : ℂ) * I) ≠ 0 := mul_ne_zero h4' I_ne_zero
    simp only [hN]
    field_simp
    ring
  rw [hfun]
  have hi1 : Integrable (fun t : ℝ => F z * (((4 * α : ℝ) : ℂ) * I * ((o t : ℝ) : ℂ))) :=
    (hoint.const_mul _).const_mul _
  have hi2 : Integrable (fun t : ℝ => D * (((-(4 * α) : ℝ) : ℂ) * ((q t : ℝ) : ℂ) +
      ((-(4 * α ^ 2) : ℝ) : ℂ) * I * ((o t : ℝ) : ℂ))) :=
    ((hqint.const_mul _).add (hoint.const_mul _)).const_mul _
  have hi12 : Integrable (fun t : ℝ => Φ (b + t * I) +
      F z * (((4 * α : ℝ) : ℂ) * I * ((o t : ℝ) : ℂ))) := hΦint.add hi1
  have hqo1 : Integrable (fun t : ℝ => ((-(4 * α) : ℝ) : ℂ) * ((q t : ℝ) : ℂ)) := hqint.const_mul _
  have hqo2 : Integrable (fun t : ℝ => ((-(4 * α ^ 2) : ℝ) : ℂ) * I * ((o t : ℝ) : ℂ)) :=
    hoint.const_mul _
  refine ⟨(hi12.add hi2).const_mul _, ?_⟩
  rw [integral_const_mul, integral_add hi12 hi2, integral_add hΦint hi1, hΦ0,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_add hqo1 hqo2, integral_const_mul, integral_const_mul,
    hoval, hqval]
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  push_cast
  field_simp
  linear_combination (-(4:ℂ) * Real.pi * D) * I_sq

end Contour

end

section
open Complex MeasureTheory Filter Topology Set

namespace ZetaLog

/-- `(s-1) ζ(s) / s`, with its removable value `1` at `s = 1`. -/
noncomputable def G0 (s : ℂ) : ℂ := if s = 1 then 1 else (s - 1) * riemannZeta s / s

lemma G0_of_ne {s : ℂ} (h : s ≠ 1) : G0 s = (s - 1) * riemannZeta s / s := by simp [G0, h]

lemma G0_one : G0 1 = 1 := by simp [G0]

lemma tendsto_G0 : Tendsto G0 (𝓝[≠] 1) (𝓝 1) := by
  have h1 := riemannZeta_residue_one
  have h2 : Tendsto (fun s : ℂ => s) (𝓝[≠] 1) (𝓝 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h3 := h1.div h2 one_ne_zero
  rw [div_one] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [G0_of_ne hs]; rfl

lemma continuousAt_G0_one : ContinuousAt G0 1 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, G0_one]
  exact tendsto_G0

lemma differentiableAt_G0 {s : ℂ} (h1 : s ≠ 1) (h0 : s ≠ 0) : DifferentiableAt ℂ G0 s := by
  have : DifferentiableAt ℂ (fun s => (s - 1) * riemannZeta s / s) s :=
    ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta h1)).div
      differentiableAt_id h0
  refine this.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds h1] with x hx
  exact G0_of_ne hx

lemma differentiableOn_G0 : DifferentiableOn ℂ G0 {s : ℂ | 0 < s.re} := by
  have hmem : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff hmem]
  refine ⟨fun s hs => ?_, continuousAt_G0_one⟩
  have h0 : s ≠ 0 := by
    rintro rfl; have := hs.1; simp at this
  exact (differentiableAt_G0 hs.2 h0).differentiableWithinAt

lemma G0_ne_zero (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) : G0 s ≠ 0 := by
  by_cases h1 : s = 1
  · simp [G0, h1]
  rw [G0_of_ne h1]
  have hz : riemannZeta s ≠ 0 := by
    intro hz
    have := hRH s hz ?_ h1
    · linarith
    · rintro ⟨n, rfl⟩
      have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [this] at hs
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.2 h1) hz) h0

/-- The half-plane `Re s > 1/2`. -/
def U : Set ℂ := {s : ℂ | 1 / 2 < s.re}

lemma isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_re

lemma U_sub {s : ℂ} (hs : s ∈ U) : 0 < s.re := by
  have : 1 / 2 < s.re := hs; linarith

lemma isSimplyConnected_U : IsSimplyConnected U := by
  have := (convex_halfSpace_re_gt (1 / 2 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
  exact (inferInstance : SimplyConnectedSpace ↥{c : ℂ | 1 / 2 < c.re})

lemma isPreconnected_U : IsPreconnected U :=
  (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected

/-- A real continuous integer-valued function on a preconnected set is constant. -/
lemma const_of_int_valued {S : Set ℂ} (hS : IsPreconnected S) {g : ℂ → ℝ}
    (hg : ContinuousOn g S) (hint : ∀ s ∈ S, ∃ n : ℤ, g s = n) :
    ∀ a ∈ S, ∀ b ∈ S, g a = g b := by
  have key : ∀ a ∈ S, ∀ b ∈ S, g a ≤ g b → g a = g b := by
    intro a ha b hb hab
    obtain ⟨m, hm⟩ := hint a ha
    obtain ⟨n, hn⟩ := hint b hb
    by_contra hne
    have hlt : g a < g b := lt_of_le_of_ne hab hne
    rw [hm, hn] at hlt
    have hmn : m < n := by exact_mod_cast hlt
    have hmem : (m : ℝ) + 1 / 2 ∈ Icc (g a) (g b) := by
      rw [hm, hn]
      constructor
      · linarith
      · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
        linarith
    obtain ⟨c, hc, hgc⟩ := hS.intermediate_value ha hb hg hmem
    obtain ⟨k, hk⟩ := hint c hc
    rw [hk] at hgc
    have h1 : (m : ℝ) < k := by linarith
    have h2 : (k : ℝ) < m + 1 := by linarith
    have h1' : m < k := by exact_mod_cast h1
    have h2' : k < m + 1 := by exact_mod_cast h2
    omega
  intro a ha b hb
  rcases le_total (g a) (g b) with h | h
  · exact key a ha b hb h
  · exact (key b hb a ha h).symm

/-- Two continuous logarithms of the same function on a preconnected set, agreeing at one point,
agree everywhere. -/
lemma log_unique {S : Set ℂ} (hS : IsPreconnected S) {F1 F2 : ℂ → ℂ}
    (h1 : ContinuousOn F1 S) (h2 : ContinuousOn F2 S)
    (he : ∀ s ∈ S, exp (F1 s) = exp (F2 s)) {a : ℂ} (ha : a ∈ S) (hfa : F1 a = F2 a) :
    ∀ s ∈ S, F1 s = F2 s := by
  have hn : ∀ s ∈ S, ∃ n : ℤ, F1 s - F2 s = n * (2 * Real.pi * I) := by
    intro s hs
    rw [← Complex.exp_eq_one_iff, exp_sub, he s hs, div_self (exp_ne_zero _)]
  set g : ℂ → ℝ := fun s => (F1 s - F2 s).im / (2 * Real.pi) with hg
  have hgc : ContinuousOn g S :=
    ((Complex.continuous_im.comp_continuousOn (h1.sub h2))).div_const _
  have hgint : ∀ s ∈ S, ∃ n : ℤ, g s = n := by
    intro s hs
    obtain ⟨n, hn⟩ := hn s hs
    refine ⟨n, ?_⟩
    simp only [hg, hn]
    simp [Real.pi_ne_zero]
  intro s hs
  have hconst := const_of_int_valued hS hgc hgint s hs a ha
  obtain ⟨n, hns⟩ := hn s hs
  have hga : g a = 0 := by simp [hg, hfa]
  have : g s = n := by simp only [hg, hns]; simp [Real.pi_ne_zero]
  rw [hconst, hga] at this
  have hn0 : n = 0 := by exact_mod_cast this.symm
  rw [hn0] at hns
  simpa [sub_eq_zero] using hns

/-- A continuous logarithm of a holomorphic function is holomorphic, with the expected derivative. -/
lemma hasDerivAt_of_exp_eq {S : Set ℂ} (hU : IsOpen S) {F G : ℂ → ℂ} (hF : ContinuousOn F S)
    (hG : DifferentiableOn ℂ G S) (h : ∀ s ∈ S, exp (F s) = G s) {s0 : ℂ} (hs0 : s0 ∈ S) :
    HasDerivAt F (deriv G s0 / G s0) s0 := by
  have hFc : ContinuousAt F s0 := hF.continuousAt (hU.mem_nhds hs0)
  have hGd : DifferentiableAt ℂ G s0 := hG.differentiableAt (hU.mem_nhds hs0)
  have hG0 : G s0 ≠ 0 := by rw [← h s0 hs0]; exact exp_ne_zero _
  set c := exp (-F s0) with hc
  have hc0 : c ≠ 0 := exp_ne_zero _
  have hw : HasDerivAt (fun s => G s * c) (deriv G s0 * c) s0 := hGd.hasDerivAt.mul_const c
  have hw1 : G s0 * c = 1 := by rw [← h s0 hs0, hc, ← exp_add]; simp
  have hlog : HasDerivAt (fun s => log (G s * c)) (deriv G s0 * c / (G s0 * c)) s0 :=
    hw.clog (by rw [hw1]; exact one_mem_slitPlane)
  have hev : ∀ᶠ s in 𝓝 s0, F s = F s0 + log (G s * c) := by
    have h1 : ∀ᶠ s in 𝓝 s0, F s ∈ Metric.ball (F s0) 1 :=
      hFc.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [h1, hU.mem_nhds hs0] with s hs hsU
    have hsm : ‖F s - F s0‖ < 1 := by rw [← dist_eq_norm]; exact hs
    have him : |(F s - F s0).im| < 1 := lt_of_le_of_lt (Complex.abs_im_le_norm _) hsm
    have : G s * c = exp (F s - F s0) := by rw [← h s hsU, hc, sub_eq_add_neg, exp_add]
    rw [this, log_exp]
    · ring
    · have := neg_abs_le (F s - F s0).im
      linarith [Real.pi_gt_three]
    · have := le_abs_self (F s - F s0).im
      linarith [Real.pi_gt_three]
  have := (hlog.const_add (F s0)).congr_of_eventuallyEq hev
  refine this.congr_deriv ?_
  have hc' : c = (G s0)⁻¹ := eq_inv_of_mul_eq_one_right hw1
  rw [hw1, hc']
  field_simp

end ZetaLog

end

section
open Complex MeasureTheory Filter Topology Set LSeries

namespace ZetaLog

lemma term_le_of_two_le {f : ℕ → ℂ} {s : ℂ} (hs : 2 ≤ s.re) (n : ℕ) (hn : n ≠ 1) :
    ‖term f s n‖ ≤ (2 : ℝ) ^ (2 - s.re) * ‖term f 2 n‖ := by
  rw [norm_term_eq, norm_term_eq]
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  have hn2 : (2 : ℝ) ≤ n := by
    have : 2 ≤ n := by omega
    exact_mod_cast this
  simp only [h0, if_false]
  have hre2 : (2 : ℂ).re = 2 := by norm_num
  rw [hre2]
  have hnpos : (0 : ℝ) < n := by linarith
  have key : (2 : ℝ) ^ (s.re - 2) * (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.re := by
    have h1 : (2 : ℝ) ^ (s.re - 2) ≤ (n : ℝ) ^ (s.re - 2) :=
      Real.rpow_le_rpow (by norm_num) hn2 (by linarith)
    calc (2 : ℝ) ^ (s.re - 2) * (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (s.re - 2) * (n : ℝ) ^ (2 : ℝ) := by
          gcongr
      _ = (n : ℝ) ^ s.re := by rw [← Real.rpow_add hnpos]; ring_nf
  have h2 : (2 : ℝ) ^ (2 - s.re) = ((2 : ℝ) ^ (s.re - 2))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]; ring_nf
  rw [h2]
  have hp1 : 0 < (2 : ℝ) ^ (s.re - 2) := by positivity
  have hp2 : 0 < (n : ℝ) ^ (2 : ℝ) := by positivity
  rw [inv_mul_eq_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [mul_comm ((n : ℝ) ^ (2 : ℝ))]
  exact mul_le_mul_of_nonneg_left key (norm_nonneg _)

lemma norm_LSeries_sub_le {f : ℕ → ℂ} (hf : LSeriesSummable f 2) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LSeries f s - f 1‖ ≤ (2 : ℝ) ^ (2 - s.re) * ∑' n, ‖term f 2 n‖ := by
  have hsum_s : LSeriesSummable f s := hf.of_re_le_re (by simpa using hs)
  have hdecomp := hsum_s.tsum_eq_add_tsum_ite 1
  have h1 : term f s 1 = f 1 := by simp
  have hL : LSeries f s - f 1 = ∑' n, (if n = 1 then 0 else term f s n) := by
    rw [LSeries, hdecomp, h1]; ring
  have hle : ∀ n, ‖(if n = 1 then (0 : ℂ) else term f s n)‖ ≤ (2 : ℝ) ^ (2 - s.re) * ‖term f 2 n‖ := by
    intro n
    split_ifs with h
    · simp only [norm_zero]; positivity
    · exact term_le_of_two_le hs n h
  have hsumn : Summable (fun n => (2 : ℝ) ^ (2 - s.re) * ‖term f 2 n‖) :=
    hf.norm.mul_left _
  have hsum2 : Summable (fun n => ‖(if n = 1 then (0 : ℂ) else term f s n)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsumn
  rw [hL]
  calc ‖∑' n, (if n = 1 then (0 : ℂ) else term f s n)‖
      ≤ ∑' n, ‖(if n = 1 then (0 : ℂ) else term f s n)‖ := norm_tsum_le_tsum_norm hsum2
    _ ≤ ∑' n, (2 : ℝ) ^ (2 - s.re) * ‖term f 2 n‖ := hsum2.tsum_le_tsum hle hsumn
    _ = (2 : ℝ) ^ (2 - s.re) * ∑' n, ‖term f 2 n‖ := tsum_mul_left

lemma zeta_sub_one_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 2 ≤ s.re →
    ‖riemannZeta s - 1‖ ≤ (2 : ℝ) ^ (2 - s.re) * K := by
  have hf : LSeriesSummable 1 2 := LSeriesSummable_one_iff.2 (by norm_num)
  refine ⟨∑' n, ‖term 1 2 n‖, tsum_nonneg (fun _ => norm_nonneg _), fun s hs => ?_⟩
  have := norm_LSeries_sub_le hf hs
  rwa [LSeries_one_eq_riemannZeta (by linarith), Pi.one_apply] at this

open ArithmeticFunction in
lemma logDeriv_zeta_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 2 ≤ s.re →
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ (2 : ℝ) ^ (2 - s.re) * K := by
  have hf : LSeriesSummable (fun n => (vonMangoldt n : ℂ)) 2 :=
    LSeriesSummable_vonMangoldt (by norm_num)
  refine ⟨∑' n, ‖term (fun n => (vonMangoldt n : ℂ)) 2 n‖, tsum_nonneg (fun _ => norm_nonneg _),
    fun s hs => ?_⟩
  have := norm_LSeries_sub_le hf hs
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by linarith)] at this
  simpa [vonMangoldt_apply_one, neg_div] using this

lemma two_rpow_tendsto : Tendsto (fun σ : ℝ => (2 : ℝ) ^ (2 - σ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun σ : ℝ => 2 + -σ) atTop atBot :=
    tendsto_atBot_add_const_left atTop 2 tendsto_neg_atTop_atBot
  have h2 := (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp h1
  refine h2.congr (fun σ => ?_)
  simp only [Function.comp, sub_eq_add_neg]

/-- `G0` is close to `1` far to the right, uniformly. -/
lemma G0_near_one : ∀ ε > 0, ∃ R : ℝ, 2 ≤ R ∧ ∀ s : ℂ, R ≤ s.re → ‖G0 s - 1‖ ≤ ε := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := zeta_sub_one_le
  have hlim : Tendsto (fun σ : ℝ => (2 : ℝ) ^ (2 - σ) * K + (1 + (2 : ℝ) ^ (2 - σ) * K) / σ)
      atTop (𝓝 (0 * K + (1 + 0 * K) * 0)) := by
    refine (two_rpow_tendsto.mul_const K).add ?_
    rw [show (fun σ : ℝ => (1 + (2 : ℝ) ^ (2 - σ) * K) / σ) =
      fun σ => (1 + (2 : ℝ) ^ (2 - σ) * K) * σ⁻¹ by funext σ; ring]
    exact (tendsto_const_nhds.add (two_rpow_tendsto.mul_const K)).mul tendsto_inv_atTop_zero
  simp only [zero_mul, add_zero, mul_zero] at hlim
  obtain ⟨R1, hR1⟩ := (eventually_atTop.1 (hlim.eventually (ge_mem_nhds hε)))
  refine ⟨max R1 2, le_max_right _ _, fun s hs => ?_⟩
  have hs2 : 2 ≤ s.re := le_trans (le_max_right _ _) hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs2; norm_num at hs2
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs2; norm_num at hs2
  have hb := hR1 s.re (le_trans (le_max_left _ _) hs)
  have hz := hK s hs2
  have hσ : 0 < s.re := by linarith
  rw [G0_of_ne hs1]
  have heq : (s - 1) * riemannZeta s / s - 1 = (riemannZeta s - 1) - riemannZeta s / s := by
    field_simp; ring
  rw [heq]
  have hzn : ‖riemannZeta s‖ ≤ 1 + (2 : ℝ) ^ (2 - s.re) * K := by
    have := norm_sub_norm_le (riemannZeta s) 1
    simp at this; linarith
  have hsn : s.re ≤ ‖s‖ := Complex.re_le_norm s
  calc ‖(riemannZeta s - 1) - riemannZeta s / s‖ ≤ ‖riemannZeta s - 1‖ + ‖riemannZeta s / s‖ :=
        norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ (2 - s.re) * K + (1 + (2 : ℝ) ^ (2 - s.re) * K) / s.re := by
        gcongr
        rw [norm_div]
        calc ‖riemannZeta s‖ / ‖s‖ ≤ (1 + (2 : ℝ) ^ (2 - s.re) * K) / ‖s‖ := by gcongr
          _ ≤ (1 + (2 : ℝ) ^ (2 - s.re) * K) / s.re := by
            apply div_le_div_of_nonneg_left (by positivity) hσ hsn
    _ ≤ ε := hb

lemma tendsto_G0_line (t : ℝ) : Tendsto (fun u : ℝ => G0 (u + t * I)) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, -, hR⟩ := G0_near_one (ε / 2) (by linarith)
  filter_upwards [eventually_ge_atTop R] with u hu
  have := hR (u + t * I) (by simpa using hu)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- The derivative of `log G0`. -/
lemma logDeriv_G0 {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hz : riemannZeta s ≠ 0) :
    deriv G0 s / G0 s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - 1 / s := by
  have hev : G0 =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s / s := by
    filter_upwards [eventually_ne_nhds hs1] with x hx
    exact G0_of_ne hx
  have hd : HasDerivAt (fun s => (s - 1) * riemannZeta s / s)
      ((((1 : ℂ) * riemannZeta s + (s - 1) * deriv riemannZeta s) * s -
        (s - 1) * riemannZeta s * 1) / s ^ 2) s := by
    have h1 : HasDerivAt (fun s : ℂ => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have h2 := (differentiableAt_riemannZeta hs1).hasDerivAt
    exact (h1.mul h2).div (hasDerivAt_id s) hs0
  rw [hev.deriv_eq, hd.deriv, G0_of_ne hs1]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  field_simp
  ring

lemma deriv_G0_one : deriv G0 1 = (Real.eulerMascheroniConstant : ℂ) - 1 := by
  have hmem : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  have hd : HasDerivAt G0 (deriv G0 1) 1 :=
    (differentiableOn_G0.differentiableAt hmem).hasDerivAt
  have h1 := hd.tendsto_slope
  have h2 : Tendsto (slope G0 1) (𝓝[≠] 1) (𝓝 ((Real.eulerMascheroniConstant - 1) / 1)) := by
    have hz := tendsto_riemannZeta_sub_one_div
    have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] 1) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have := (hz.sub_const 1).div hid one_ne_zero
    refine this.congr' ?_
    have h0 : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 0 :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.eventually (eventually_ne_nhds one_ne_zero)
    filter_upwards [self_mem_nhdsWithin, h0] with s hs hs0
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
    rw [slope_def_field, G0_of_ne hs, G0_one]
    simp only [Pi.div_apply]
    field_simp
    ring
  rw [div_one] at h2
  exact tendsto_nhds_unique h1 h2

end ZetaLog

end

section
open Complex MeasureTheory Filter Topology Set ComplexConjugate

namespace ZetaLog

/-- Properties of a holomorphic logarithm of `G0` on the half-plane `Re s > 1/2`. -/
structure IsLogG0 (F : ℂ → ℂ) : Prop where
  exp_eq : ∀ s ∈ U, exp (F s) = G0 s
  hasDeriv : ∀ s ∈ U, HasDerivAt F (deriv G0 s / G0 s) s
  conj_eq : ∀ s ∈ U, F (conj s) = conj (F s)
  right : ∃ R : ℝ, 2 ≤ R ∧ ∀ s : ℂ, R ≤ s.re → F s = log (G0 s) ∧ ‖G0 s - 1‖ ≤ 1 / 2

lemma mem_U {s : ℂ} : s ∈ U ↔ 1 / 2 < s.re := Iff.rfl

lemma G0_conj (s : ℂ) : G0 (conj s) = conj (G0 s) := by
  by_cases h : s = 1
  · subst h; simp [G0_one]
  have h' : conj s ≠ 1 := by
    intro h2; apply h; simpa using congrArg conj h2
  rw [G0_of_ne h, G0_of_ne h', riemannZeta_conj]
  simp [map_div₀]

lemma slitPlane_of_near_one {w : ℂ} (h : ‖w - 1‖ ≤ 1 / 2) : w ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  have := Complex.abs_re_le_norm (w - 1)
  rw [sub_re, one_re] at this
  have := abs_le.1 (this.trans h)
  linarith

lemma arg_ne_pi_of_near_one {w : ℂ} (h : ‖w - 1‖ ≤ 1 / 2) : w.arg ≠ Real.pi := by
  have hw := slitPlane_of_near_one h
  exact (mem_slitPlane_iff_arg.1 hw).1

theorem exists_logG0 (hRH : RiemannHypothesis) : ∃ F : ℂ → ℂ, IsLogG0 F := by
  have hGd : DifferentiableOn ℂ G0 U := differentiableOn_G0.mono (fun s hs => U_sub hs)
  have hGc : ContinuousOn G0 U := hGd.continuousOn
  have h0 : (0 : ℂ) ∉ G0 '' U := by
    rintro ⟨s, hs, h⟩; exact G0_ne_zero hRH hs h
  obtain ⟨F1, hF1c, hF1e⟩ := Complex.exists_continuousOn_eqOn_exp_comp isSimplyConnected_U
    isOpen_U hGc h0
  obtain ⟨R, hR2, hR⟩ := G0_near_one (1 / 2) (by norm_num)
  set a0 : ℂ := (R : ℂ) with ha0
  have ha0U : a0 ∈ U := by show 1 / 2 < a0.re; simp [ha0]; linarith
  have ha0R : R ≤ a0.re := by simp [ha0]
  set F : ℂ → ℂ := fun s => F1 s - (F1 a0 - log (G0 a0)) with hF
  have hGa0 : G0 a0 ≠ 0 := G0_ne_zero hRH ha0U
  have hFc : ContinuousOn F U := hF1c.sub continuousOn_const
  have hFe : ∀ s ∈ U, exp (F s) = G0 s := by
    intro s hs
    have h1 : exp (F1 s) = G0 s := hF1e hs
    have h2 : exp (F1 a0) = G0 a0 := hF1e ha0U
    simp only [hF]
    rw [exp_sub, exp_sub, exp_log hGa0, h1, h2]
    field_simp
  have hFa0 : F a0 = log (G0 a0) := by simp [hF]
  -- agreement with the principal logarithm far right
  have hVc : IsPreconnected {s : ℂ | R ≤ s.re} :=
    (convex_halfSpace_re_ge R).isPreconnected
  have hVU : {s : ℂ | R ≤ s.re} ⊆ U := by
    intro s hs; show 1 / 2 < s.re; have : R ≤ s.re := hs; linarith
  have hlogc : ContinuousOn (fun s => log (G0 s)) {s : ℂ | R ≤ s.re} :=
    (hGc.mono hVU).clog (fun s hs => slitPlane_of_near_one (hR s hs))
  have hagree := log_unique hVc (hFc.mono hVU) hlogc
    (fun s hs => by rw [hFe s (hVU hs), exp_log (G0_ne_zero hRH (hVU hs))]) ha0R hFa0
  refine ⟨F, hFe, fun s hs => hasDerivAt_of_exp_eq isOpen_U hFc hGd hFe hs, ?_,
    ⟨R, hR2, fun s hs => ⟨hagree s hs, hR s hs⟩⟩⟩
  -- conjugation symmetry
  have hconjU : ∀ s ∈ U, conj s ∈ U := by
    intro s hs; show 1 / 2 < (conj s).re; rw [conj_re]; exact hs
  set F2 : ℂ → ℂ := fun s => conj (F (conj s)) with hF2
  have hF2c : ContinuousOn F2 U := by
    have h1 : ContinuousOn (fun s => F (conj s)) U :=
      hFc.comp Complex.continuous_conj.continuousOn hconjU
    exact Complex.continuous_conj.comp_continuousOn h1
  have hF2e : ∀ s ∈ U, exp (F2 s) = exp (F s) := by
    intro s hs
    simp only [hF2]
    rw [exp_conj, hFe _ (hconjU s hs), hFe s hs, G0_conj, conj_conj]
  have hF2a0 : F2 a0 = F a0 := by
    simp only [hF2]
    have hc : conj a0 = a0 := by simp [ha0]
    rw [hc, hFa0]
    have hreal : conj (G0 a0) = G0 a0 := by rw [← G0_conj, hc]
    rw [← log_conj _ (arg_ne_pi_of_near_one (hR a0 ha0R)), hreal]
  have := log_unique isPreconnected_U hF2c hFc hF2e ha0U hF2a0
  intro s hs
  have h1 := this (conj s) (hconjU s hs)
  simp only [hF2, conj_conj] at h1
  rw [← h1]

/-- Continuity of `ζ'/ζ` away from `1` and from zeros. -/
lemma continuousAt_logDeriv_zeta {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    ContinuousAt (fun s => deriv riemannZeta s / riemannZeta s) s := by
  have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun x hx =>
    (differentiableAt_riemannZeta hx).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv riemannZeta) {1}ᶜ := hd.deriv hopen
  have h1 : ContinuousAt (deriv riemannZeta) s :=
    (hdd.differentiableAt (hopen.mem_nhds hs1)).continuousAt
  exact h1.div (differentiableAt_riemannZeta hs1).continuousAt hz

lemma zeta_ne_zero_of_U (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have h := G0_ne_zero hRH hs
  rw [G0_of_ne hs1, hz] at h
  simp at h

lemma deriv_F_eq (hRH : RiemannHypothesis) {F : ℂ → ℂ} (hF : IsLogG0 F) {s : ℂ} (hs : s ∈ U)
    (hs1 : s ≠ 1) :
    deriv F s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - 1 / s := by
  rw [(hF.hasDeriv s hs).deriv]
  have hs0 : s ≠ 0 := by intro h; have := U_sub hs; rw [h] at this; simp at this
  exact logDeriv_G0 hs1 hs0 (zeta_ne_zero_of_U hRH hs hs1)

lemma tendsto_F_line {F : ℂ → ℂ} (hF : IsLogG0 F) (t : ℝ) :
    Tendsto (fun u : ℝ => F (u + t * I)) atTop (𝓝 0) := by
  obtain ⟨R, -, hR⟩ := hF.right
  have h1 : Tendsto (fun u : ℝ => log (G0 (u + t * I))) atTop (𝓝 (log 1)) :=
    ((continuousAt_clog one_mem_slitPlane).tendsto).comp (tendsto_G0_line t)
  rw [log_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop R] with u hu
  exact ((hR (u + t * I) (by simpa using hu)).1).symm

/-- Sublinear growth of the logarithm on closed half-planes `Re s ≥ b > 1/2`, under RH. -/
theorem F_growth (hRH : RiemannHypothesis) {F : ℂ → ℂ} (hF : IsLogG0 F) {b : ℝ}
    (hb : 1 / 2 < b) :
    ∃ C : ℝ, ∀ s : ℂ, b ≤ s.re → ‖F s‖ ≤ C * (1 + ‖s‖) ^ (1 / 2 : ℝ) := by
  obtain ⟨R, hR2, hR⟩ := hF.right
  obtain ⟨CT, hCT⟩ := Titchmarsh.logDeriv_riemannZeta_le_log_of_riemannHypothesis hRH (b - 1 / 2)
    (by linarith)
  obtain ⟨K2, hK20, hK2⟩ := logDeriv_zeta_le
  -- compact part
  have hKc : IsCompact {s : ℂ | b ≤ s.re ∧ s.re ≤ R ∧ |s.im| ≤ 2} := by
    have : {s : ℂ | b ≤ s.re ∧ s.re ≤ R ∧ |s.im| ≤ 2} = Set.Icc b R ×ℂ Set.Icc (-2) 2 := by
      ext s; simp [mem_reProdIm, abs_le]; tauto
    rw [this]; exact isCompact_Icc.reProdIm isCompact_Icc
  have hFcU : ContinuousOn F U := fun s hs => (hF.hasDeriv s hs).continuousAt.continuousWithinAt
  obtain ⟨M1, hM1⟩ := hKc.exists_bound_of_continuousOn (hFcU.mono (fun s hs => by
    show 1 / 2 < s.re; linarith [hs.1]))
  refine ⟨3 / 4 + R * (K2 + 2) + 2 * R * |CT| + |M1|, fun s hs => ?_⟩
  have hS1 : 1 ≤ (1 + ‖s‖) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [norm_nonneg s])
    (by norm_num)
  have hpos : 0 ≤ 3 / 4 + R * (K2 + 2) + 2 * R * |CT| := by
    have : 0 ≤ R := by linarith
    positivity
  -- far right
  by_cases hsR : R ≤ s.re
  · obtain ⟨h1, h2⟩ := hR s hsR
    have : ‖F s‖ ≤ 3 / 4 := by
      rw [h1]
      have := norm_log_one_add_half_le_self (z := G0 s - 1) h2
      rw [add_sub_cancel] at this
      linarith
    calc ‖F s‖ ≤ 3 / 4 := this
      _ ≤ (3 / 4 + R * (K2 + 2) + 2 * R * |CT| + |M1|) * 1 := by
          have : 0 ≤ R * (K2 + 2) + 2 * R * |CT| + |M1| := by
            have : 0 ≤ R := by linarith
            positivity
          linarith
      _ ≤ _ := by gcongr
  push Not at hsR
  by_cases ht : |s.im| ≤ 2
  · have := hM1 s ⟨hs, hsR.le, ht⟩
    calc ‖F s‖ ≤ |M1| := this.trans (le_abs_self _)
      _ ≤ (3 / 4 + R * (K2 + 2) + 2 * R * |CT| + |M1|) * 1 := by linarith
      _ ≤ _ := by gcongr
  push Not at ht
  -- horizontal mean value estimate
  set t := s.im
  set σ := s.re
  have hsσ : s = (σ : ℂ) + t * I := (Complex.re_add_im s).symm
  set f : ℝ → ℂ := fun u => F (u + t * I) with hf
  have hlogt : Real.log |t| ≤ 2 * (1 + ‖s‖) ^ (1 / 2 : ℝ) := by
    have h1 := Real.log_le_rpow_div (abs_nonneg t) (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 : |t| ^ (1 / 2 : ℝ) ≤ (1 + ‖s‖) ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow (abs_nonneg t) _ (by norm_num)
      have := Complex.abs_im_le_norm s; linarith
    linarith
  have hlog0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
  set B := |CT| * Real.log |t| + K2 + 2 with hB
  have hderiv : ∀ u ∈ Icc σ R, HasDerivWithinAt f (deriv F (u + t * I)) (Icc σ R) u := by
    intro u hu
    have hmem : (u : ℂ) + t * I ∈ U := by
      show 1 / 2 < ((u : ℂ) + t * I).re; simp; linarith [hu.1]
    have h1 := (hF.hasDeriv _ hmem)
    rw [← h1.deriv] at h1
    have h2 : HasDerivAt (fun w : ℂ => F (w + t * I)) (deriv F (u + t * I)) (u : ℂ) := by
      have := h1.comp_add_const (u : ℂ) (t * I)
      simpa using this
    exact (h2.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ u ∈ Ico σ R, ‖deriv F (u + t * I)‖ ≤ B := by
    intro u hu
    have hmem : (u : ℂ) + t * I ∈ U := by
      show 1 / 2 < ((u : ℂ) + t * I).re; simp; linarith [hu.1]
    have hne1 : (u : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; rw [this] at ht; norm_num at ht
    rw [deriv_F_eq hRH hF hmem hne1]
    have hn1 : 1 ≤ ‖(u : ℂ) + t * I - 1‖ := by
      have := Complex.abs_im_le_norm ((u : ℂ) + t * I - 1)
      simp at this; linarith
    have hn0 : 1 ≤ ‖(u : ℂ) + t * I‖ := by
      have := Complex.abs_im_le_norm ((u : ℂ) + t * I)
      simp at this; linarith
    have hz : ‖deriv riemannZeta ((u : ℂ) + t * I) / riemannZeta ((u : ℂ) + t * I)‖ ≤
        |CT| * Real.log |t| + K2 := by
      by_cases hu2 : u ≤ 2
      · have := hCT ((u : ℂ) + t * I) (by simp; linarith [hu.1]) (by simpa using hu2)
          (by simpa using ht.le)
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
          add_zero, zero_add] at this
        calc _ ≤ CT * Real.log |t| := this
          _ ≤ |CT| * Real.log |t| := by gcongr; exact le_abs_self _
          _ ≤ _ := by linarith
      · push Not at hu2
        have := hK2 ((u : ℂ) + t * I) (by simp; linarith)
        have h2 : (2 : ℝ) ^ (2 - ((u : ℂ) + t * I).re) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num); simp; linarith
        have : ‖deriv riemannZeta ((u : ℂ) + t * I) / riemannZeta ((u : ℂ) + t * I)‖ ≤ K2 :=
          this.trans (by nlinarith)
        have : 0 ≤ |CT| * Real.log |t| := by positivity
        linarith
    calc _ ≤ ‖deriv riemannZeta ((u : ℂ) + t * I) / riemannZeta ((u : ℂ) + t * I) +
          1 / ((u : ℂ) + t * I - 1)‖ + ‖1 / ((u : ℂ) + t * I)‖ := norm_sub_le _ _
      _ ≤ ‖deriv riemannZeta ((u : ℂ) + t * I) / riemannZeta ((u : ℂ) + t * I)‖ +
          ‖1 / ((u : ℂ) + t * I - 1)‖ + ‖1 / ((u : ℂ) + t * I)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (|CT| * Real.log |t| + K2) + 1 + 1 := by
          gcongr
          · rw [norm_div, norm_one]; exact div_le_one_of_le₀ hn1 (by positivity)
          · rw [norm_div, norm_one]; exact div_le_one_of_le₀ hn0 (by positivity)
      _ = B := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound R ⟨hsR.le, le_rfl⟩
  have hfR : ‖f R‖ ≤ 3 / 4 := by
    obtain ⟨h1, h2⟩ := hR ((R : ℂ) + t * I) (by simp)
    simp only [hf]; rw [h1]
    have := norm_log_one_add_half_le_self (z := G0 ((R : ℂ) + t * I) - 1) h2
    rw [add_sub_cancel] at this; linarith
  have hfs : f σ = F s := by simp only [hf]; rw [← hsσ]
  have hσ0 : 0 < σ := by linarith
  have hB0 : 0 ≤ B := by positivity
  calc ‖F s‖ = ‖f σ‖ := by rw [hfs]
    _ ≤ ‖f R‖ + ‖f R - f σ‖ := by
        have := norm_sub_le (f R) (f R - f σ); simp at this; linarith [norm_sub_rev (f R) (f σ)]
    _ ≤ 3 / 4 + B * (R - σ) := by
        gcongr
    _ ≤ 3 / 4 + B * R := by gcongr; linarith
    _ = 3 / 4 + R * (K2 + 2) + R * |CT| * Real.log |t| := by rw [hB]; ring
    _ ≤ 3 / 4 + R * (K2 + 2) + R * |CT| * (2 * (1 + ‖s‖) ^ (1 / 2 : ℝ)) := by
        have : 0 ≤ R * |CT| := mul_nonneg (by linarith) (abs_nonneg _)
        gcongr
    _ ≤ (3 / 4 + R * (K2 + 2)) * (1 + ‖s‖) ^ (1 / 2 : ℝ) +
          2 * R * |CT| * (1 + ‖s‖) ^ (1 / 2 : ℝ) := by
        have : 0 ≤ 3 / 4 + R * (K2 + 2) := by
          have : 0 ≤ R := by linarith
          positivity
        nlinarith
    _ ≤ _ := by
        have : 0 ≤ |M1| * (1 + ‖s‖) ^ (1 / 2 : ℝ) := by positivity
        nlinarith

end ZetaLog

end

section
open Complex MeasureTheory Filter Topology Set ComplexConjugate

namespace ZetaLog

lemma hasDerivAt_line {e : ℂ → ℂ} {e' : ℂ} {u t : ℝ} (h : HasDerivAt e e' ((u : ℂ) + t * I)) :
    HasDerivAt (fun v : ℝ => e ((v : ℂ) + t * I)) e' u := by
  have h2 : HasDerivAt (fun w : ℂ => e (w + t * I)) e' (u : ℂ) := by
    simpa using h.comp_add_const (u : ℂ) (t * I)
  exact h2.comp_ofReal

lemma line_mem_slitPlane {v t : ℝ} (ht : t ≠ 0) : (v : ℂ) + t * I ∈ slitPlane := by
  rw [mem_slitPlane_iff]; right; simpa using ht

lemma line_sub_one_mem_slitPlane {v t : ℝ} (ht : t ≠ 0) : (v : ℂ) + t * I - 1 ∈ slitPlane := by
  rw [mem_slitPlane_iff]; right; simpa using ht

/-- `‖log (v + it) - log (v - 1 + it)‖ ≤ 1/|t|`. -/
lemma norm_log_diff_le {v t : ℝ} (ht : t ≠ 0) :
    ‖log ((v : ℂ) + t * I) - log ((v : ℂ) + t * I - 1)‖ ≤ 1 / |t| := by
  set k : ℝ → ℂ := fun w => log ((w : ℂ) + t * I) with hk
  have hd : ∀ w ∈ Icc (v - 1) v, HasDerivWithinAt k (((w : ℂ) + t * I)⁻¹) (Icc (v - 1) v) w := by
    intro w _
    exact (hasDerivAt_line (hasDerivAt_log (line_mem_slitPlane ht))).hasDerivWithinAt
  have hb : ∀ w ∈ Ico (v - 1) v, ‖((w : ℂ) + t * I)⁻¹‖ ≤ 1 / |t| := by
    intro w _
    rw [norm_inv, one_div]
    have h1 : |t| ≤ ‖(w : ℂ) + t * I‖ := by
      have := Complex.abs_im_le_norm ((w : ℂ) + t * I); simpa using this
    exact inv_anti₀ (abs_pos.2 ht) h1
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb v ⟨by linarith, le_rfl⟩
  have e1 : k (v - 1) = log ((v : ℂ) + t * I - 1) := by
    simp only [hk]; congr 1; push_cast; ring
  rw [e1] at this
  simpa using this

lemma tendsto_log_diff (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun u : ℝ => log ((u : ℂ) + t * I) - log ((u : ℂ) + t * I - 1)) atTop (𝓝 0) := by
  -- mean value in the horizontal direction: bounded by `1/(u-1)`
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun u : ℝ => 1 / (u - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => u + -1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp h1
    refine this.congr (fun u => ?_); simp [sub_eq_add_neg]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_gt_atTop 2] with u hu
  set k : ℝ → ℂ := fun w => log ((w : ℂ) + t * I) with hk
  have hd : ∀ w ∈ Icc (u - 1) u, HasDerivWithinAt k (((w : ℂ) + t * I)⁻¹) (Icc (u - 1) u) w := by
    intro w _
    exact (hasDerivAt_line (hasDerivAt_log (line_mem_slitPlane ht))).hasDerivWithinAt
  have hb : ∀ w ∈ Ico (u - 1) u, ‖((w : ℂ) + t * I)⁻¹‖ ≤ 1 / (u - 1) := by
    intro w hw
    rw [norm_inv, one_div]
    have h1 : u - 1 ≤ ‖(w : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((w : ℂ) + t * I); simp at this
      have := le_abs_self w; linarith [hw.1]
    exact inv_anti₀ (by linarith) h1
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb u ⟨by linarith, le_rfl⟩
  have e1 : k (u - 1) = log ((u : ℂ) + t * I - 1) := by
    simp only [hk]; congr 1; push_cast; ring
  rw [e1] at this
  simpa using this

/-- Integrability of `ζ'/ζ` along horizontal rays, under RH. -/
lemma integrableOn_logDeriv_ray (hRH : RiemannHypothesis) {b t : ℝ} (hb : 1 / 2 < b)
    (ht : t ≠ 0) :
    IntegrableOn (fun u : ℝ => deriv riemannZeta ((u : ℂ) + t * I) / riemannZeta ((u : ℂ) + t * I))
      (Ioi b) := by
  set φ := fun u : ℝ => deriv riemannZeta ((u : ℂ) + t * I) / riemannZeta ((u : ℂ) + t * I)
  have hcont : ContinuousOn φ (Ici b) := by
    intro u hu
    have hu' : b ≤ u := hu
    have hs1 : (u : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; exact ht this
    have hz := zeta_ne_zero_of_U hRH (s := (u : ℂ) + t * I) (by simp; linarith) hs1
    have := (continuousAt_logDeriv_zeta hs1 hz).comp
      (f := fun v : ℝ => (v : ℂ) + t * I) (by fun_prop)
    exact this.continuousWithinAt
  obtain ⟨K2, hK20, hK2⟩ := logDeriv_zeta_le
  set c := max b 2
  have h1 : IntegrableOn φ (Icc b c) :=
    (hcont.mono Icc_subset_Ici_self).integrableOn_Icc
  have h2 : IntegrableOn φ (Ioi c) := by
    have hg : IntegrableOn (fun u : ℝ => 4 * K2 * Real.exp (-(Real.log 2) * u)) (Ioi c) :=
      (exp_neg_integrableOn_Ioi c (Real.log_pos (by norm_num))).const_mul _
    refine hg.mono' ((hcont.mono (fun u hu => le_of_lt (lt_of_le_of_lt (le_max_left b 2)
      hu))).aestronglyMeasurable measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun u hu => ?_)
    have hu2 : 2 ≤ u := le_trans (le_max_right b 2) (le_of_lt hu)
    have := hK2 ((u : ℂ) + t * I) (by simpa using hu2)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero] at this
    calc ‖φ u‖ ≤ (2 : ℝ) ^ (2 - u) * K2 := this
      _ = 4 * K2 * Real.exp (-(Real.log 2) * u) := by
        rw [Real.rpow_def_of_pos (by norm_num), show Real.log 2 * (2 - u) =
          2 * Real.log 2 + (-(Real.log 2) * u) by ring, Real.exp_add,
          show 2 * Real.log 2 = Real.log 4 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
          Real.exp_log (by norm_num)]
        ring
  have := h1.union h2
  refine this.mono_set (fun u hu => ?_)
  by_cases huc : u ≤ c
  · left; exact ⟨le_of_lt hu, huc⟩
  · right; exact lt_of_not_ge huc

/-- The horizontal-branch logarithm `h(b,t)` in terms of `F`, for `b > 1/2`, `t ≠ 0`. -/
theorem h_eq (hRH : RiemannHypothesis) {F : ℂ → ℂ} (hF : IsLogG0 F) {b t : ℝ} (hb : 1 / 2 < b)
    (ht : t ≠ 0) :
    -(∫ u in Ioi b, deriv riemannZeta ((u : ℂ) + t * I) / riemannZeta ((u : ℂ) + t * I)) =
      F ((b : ℂ) + t * I) + log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1) := by
  set g : ℝ → ℂ := fun u => F ((u : ℂ) + t * I) + log ((u : ℂ) + t * I) -
    log ((u : ℂ) + t * I - 1) with hg
  have hderiv : ∀ u : ℝ, b ≤ u → HasDerivAt g
      (deriv riemannZeta ((u : ℂ) + t * I) / riemannZeta ((u : ℂ) + t * I)) u := by
    intro u hu
    have hmem : (u : ℂ) + t * I ∈ U := by show 1 / 2 < ((u : ℂ) + t * I).re; simp; linarith
    have hs1 : (u : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; exact ht this
    have h1 := hasDerivAt_line (hF.hasDeriv _ hmem)
    have h2 := hasDerivAt_line (hasDerivAt_log (line_mem_slitPlane (v := u) ht))
    have h3 : HasDerivAt (fun w : ℂ => log (w - 1)) (((u : ℂ) + t * I - 1)⁻¹) ((u : ℂ) + t * I) :=
      (hasDerivAt_log (line_sub_one_mem_slitPlane (v := u) ht)).comp_sub_const _ _
    have h3' := hasDerivAt_line h3
    refine ((h1.add h2).sub h3').congr_deriv ?_
    rw [← (hF.hasDeriv _ hmem).deriv, deriv_F_eq hRH hF hmem hs1]
    have hs0 : (u : ℂ) + t * I ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; exact ht this
    have hs1' : (u : ℂ) + t * I - 1 ≠ 0 := sub_ne_zero.2 hs1
    field_simp
    ring
  have hcont : ContinuousWithinAt g (Ici b) b := (hderiv b le_rfl).continuousAt.continuousWithinAt
  have htend : Tendsto g atTop (𝓝 0) := by
    have := (tendsto_F_line hF t).add (tendsto_log_diff t ht)
    rw [add_zero] at this
    refine this.congr (fun u => ?_)
    simp only [hg]; ring
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun u hu => hderiv u (le_of_lt hu))
    (integrableOn_logDeriv_ray hRH hb ht) htend
  rw [this]
  simp only [hg]; ring

end ZetaLog

end

section
open Complex MeasureTheory Filter Topology Set ComplexConjugate

namespace ZetaLog

lemma ae_ne_zero : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
  have := (Set.countable_singleton (0 : ℝ)).ae_notMem volume
  simpa using this

lemma line_ne_zero {b t : ℝ} (hb : 0 < b) : (b : ℂ) + t * I ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith

lemma norm_line_ge {b t : ℝ} : |t| ≤ ‖(b : ℂ) + t * I‖ := by
  have := Complex.abs_im_le_norm ((b : ℂ) + t * I); simpa using this

lemma norm_line_ge_re {b t : ℝ} : |b| ≤ ‖(b : ℂ) + t * I‖ := by
  have := Complex.abs_re_le_norm ((b : ℂ) + t * I); simpa using this

lemma normSq_line {b t : ℝ} : ‖(b : ℂ) + t * I‖ ^ 2 = b ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- `‖log z‖ ≤ |log ‖z‖| + π`. -/
lemma norm_log_le (z : ℂ) : ‖log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  have h := Complex.norm_le_abs_re_add_abs_im (log z)
  rw [log_re, log_im] at h
  have := abs_arg_le_pi z
  linarith

/-- A bound for `L(t) = log(b+it) - log(b-1+it)` on the whole line. -/
lemma norm_L_le {b : ℝ} (hb : 0 < b) (hb1 : b < 1) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, t ≠ 0 →
    ‖log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)‖ ≤ K := by
  set K0 := |Real.log b| + |Real.log (b + 1)| + |Real.log (1 - b)| + |Real.log 2| + 2 * Real.pi
  refine ⟨K0 + 1, by positivity, fun t ht => ?_⟩
  by_cases h1 : |t| ≤ 1
  · -- bounded region
    have hs1 : b ≤ ‖(b : ℂ) + t * I‖ := by
      have := norm_line_ge_re (b := b) (t := t)
      rwa [abs_of_pos hb] at this
    have hs2 : ‖(b : ℂ) + t * I‖ ≤ b + 1 := by
      calc ‖(b : ℂ) + t * I‖ ≤ ‖(b : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = |b| + |t| := by simp
        _ ≤ b + 1 := by rw [abs_of_pos hb]; linarith
    have hw : (b : ℂ) + t * I - 1 = ((b - 1 : ℝ) : ℂ) + t * I := by push_cast; ring
    have hs3 : 1 - b ≤ ‖(b : ℂ) + t * I - 1‖ := by
      rw [hw]; have := norm_line_ge_re (b := b - 1) (t := t)
      rw [abs_of_neg (by linarith)] at this; linarith
    have hs4 : ‖(b : ℂ) + t * I - 1‖ ≤ 2 := by
      rw [hw]
      calc ‖((b - 1 : ℝ) : ℂ) + t * I‖ ≤ ‖((b - 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = |b - 1| + |t| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 2 := by rw [abs_of_neg (by linarith)]; linarith
    have hl1 : |Real.log ‖(b : ℂ) + t * I‖| ≤ |Real.log b| + |Real.log (b + 1)| := by
      have a1 := Real.log_le_log hb hs1
      have a2 := Real.log_le_log (by linarith) hs2
      rw [abs_le]; constructor <;> cases abs_cases (Real.log b) <;>
        cases abs_cases (Real.log (b + 1)) <;> linarith
    have hl2 : |Real.log ‖(b : ℂ) + t * I - 1‖| ≤ |Real.log (1 - b)| + |Real.log 2| := by
      have a1 := Real.log_le_log (by linarith) hs3
      have a2 := Real.log_le_log (by linarith) hs4
      rw [abs_le]; constructor <;> cases abs_cases (Real.log (1 - b)) <;>
        cases abs_cases (Real.log 2) <;> linarith
    have hn : ‖log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)‖ ≤ K0 := by
      calc _ ≤ ‖log ((b : ℂ) + t * I)‖ + ‖log ((b : ℂ) + t * I - 1)‖ := norm_sub_le _ _
        _ ≤ (|Real.log ‖(b : ℂ) + t * I‖| + Real.pi) +
            (|Real.log ‖(b : ℂ) + t * I - 1‖| + Real.pi) := add_le_add (norm_log_le _) (norm_log_le _)
        _ ≤ K0 := by simp only [K0]; linarith
    linarith
  · push Not at h1
    have := norm_log_diff_le (v := b) ht
    have hK0 : 0 ≤ K0 := by positivity
    calc _ ≤ 1 / |t| := this
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      _ ≤ K0 + 1 := by linarith

lemma hasDerivAt_E {w : ℂ} (hw0 : w ≠ 0) (hsl : w ∈ slitPlane) (hsl1 : w - 1 ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => (log z - log (z - 1)) * (1 - 1 / z) - 1 / z)
      ((log w - log (w - 1)) / w ^ 2) w := by
  have h1 : HasDerivAt (fun z => log z) w⁻¹ w := hasDerivAt_log hsl
  have h2 : HasDerivAt (fun z : ℂ => log (z - 1)) ((w - 1)⁻¹) w :=
    (hasDerivAt_log hsl1).comp_sub_const _ _
  have h3 : HasDerivAt (fun z : ℂ => 1 / z) (-(w ^ 2)⁻¹) w := by
    simpa [one_div] using hasDerivAt_inv hw0
  have h4 : HasDerivAt (fun z : ℂ => 1 - 1 / z) (-(-(w ^ 2)⁻¹)) w := h3.const_sub 1
  have := ((h1.sub h2).mul h4).sub h3
  refine this.congr_deriv ?_
  have hw1 : w - 1 ≠ 0 := slitPlane_ne_zero hsl1
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- The explicit integral `∫ (log(b+it) - log(b-1+it)) / (b+it)^2 dt = 2π (1 - 1/b)`. -/
theorem explicit_open {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable (fun t : ℝ => (log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)) /
      ((b : ℂ) + t * I) ^ 2) ∧
    ∫ t : ℝ, (log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)) / ((b : ℂ) + t * I) ^ 2 =
      2 * Real.pi * (1 - 1 / (b : ℂ)) := by
  set f : ℝ → ℂ := fun t => (log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)) /
      ((b : ℂ) + t * I) ^ 2 with hf
  obtain ⟨K, hK0, hK⟩ := norm_L_le hb hb1
  have hmeas : AEStronglyMeasurable f volume := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hf]
    fun_prop
  have hsq : ∀ t : ℝ, 1 ≤ ‖((b : ℂ) + t * I) ^ 2‖ * (1 / b ^ 2) ∨ True := fun _ => Or.inr trivial
  have hint : Integrable f := by
    refine ((Contour.integrable_inv_sq_add hb).const_mul K).mono' hmeas ?_
    filter_upwards [ae_ne_zero] with t ht
    simp only [hf]
    rw [norm_div, norm_pow, normSq_line]
    have h1 := hK t ht
    have hp : 0 < b ^ 2 + t ^ 2 := by positivity
    rw [div_le_iff₀ hp]
    calc _ ≤ K := h1
      _ = K * (1 / (b ^ 2 + t ^ 2)) * (b ^ 2 + t ^ 2) := by field_simp
  refine ⟨hint, ?_⟩
  -- antiderivative on the positive half-line
  set A : ℝ → ℂ := fun t => (log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)) *
      (1 - 1 / ((b : ℂ) + t * I)) - 1 / ((b : ℂ) + t * I) with hA
  have hAd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt A (I * f t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    set w := (b : ℂ) + t * I
    have hw0 : w ≠ 0 := line_ne_zero hb
    have hw1 : w - 1 ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp [w] at this; exact ht0 this
    have hsl := line_mem_slitPlane (v := b) ht0
    have hsl1 := line_sub_one_mem_slitPlane (v := b) ht0
    have hE := hasDerivAt_E hw0 hsl hsl1
    have hl : HasDerivAt (fun t : ℝ => (b : ℂ) + t * I) I t := by
      have := ((hasDerivAt_id t).ofReal_comp).mul_const I
      simpa using this.const_add (b : ℂ)
    have := hE.comp t hl
    refine this.congr_deriv ?_
    simp only [hf, w]; ring
  have hAc : ContinuousWithinAt A (Ici 0) 0 := by
    have hb0 : ((b : ℂ) + ((0 : ℝ) : ℂ) * I) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left; simpa using hb
    have hc1 : ContinuousAt (fun t : ℝ => log ((b : ℂ) + t * I)) 0 :=
      (continuousAt_clog hb0).comp (f := fun t : ℝ => (b : ℂ) + t * I) (by fun_prop)
    have hc2 : ContinuousWithinAt (fun t : ℝ => log ((b : ℂ) + t * I - 1)) (Ici 0) 0 := by
      have hz : ((b : ℂ) + ((0 : ℝ) : ℂ) * I - 1).re < 0 := by simp; linarith
      have hz' : ((b : ℂ) + ((0 : ℝ) : ℂ) * I - 1).im = 0 := by simp
      have := continuousWithinAt_log_of_re_neg_of_im_zero hz hz'
      refine this.comp (f := fun t : ℝ => (b : ℂ) + t * I - 1) (by fun_prop) ?_
      intro t ht; simp only [Set.mem_ofPred_eq]; simpa using ht
    have hc3 : ContinuousAt (fun t : ℝ => 1 / ((b : ℂ) + t * I)) 0 := by
      refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
      exact line_ne_zero hb
    exact ((hc1.continuousWithinAt.sub hc2).mul (continuousWithinAt_const.sub
      hc3.continuousWithinAt)).sub hc3.continuousWithinAt
  have hAt : Tendsto A atTop (𝓝 0) := by
    have hL : Tendsto (fun t : ℝ => log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)) atTop
        (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
        (tendsto_inv_atTop_zero.comp tendsto_abs_atTop_atTop)
      filter_upwards [eventually_gt_atTop 0] with t ht
      have := norm_log_diff_le (v := b) (ne_of_gt ht)
      simpa [one_div] using this
    have hinv : Tendsto (fun t : ℝ => 1 / ((b : ℂ) + t * I)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
        (tendsto_inv_atTop_zero.comp tendsto_abs_atTop_atTop)
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_div, norm_one, one_div]
      exact inv_anti₀ (abs_pos.2 (ne_of_gt ht)) norm_line_ge
    have := (hL.mul ((tendsto_const_nhds (x := (1 : ℂ))).sub hinv)).sub hinv
    simpa [hA] using this
  have hIf : IntegrableOn (fun t => I * f t) (Ioi 0) := (hint.const_mul I).integrableOn
  have hJ := integral_Ioi_of_hasDerivAt_of_tendsto hAc hAd hIf hAt
  rw [integral_const_mul] at hJ
  -- value of `A 0`
  have hA0 : A 0 = ((Real.log b : ℂ) - ((Real.log (1 - b) : ℂ) + Real.pi * I)) * (1 - 1 / (b : ℂ)) -
      1 / (b : ℂ) := by
    have e1 : log ((b : ℂ) + ((0 : ℝ) : ℂ) * I) = Real.log b := by
      simp; rw [ofReal_log hb.le]
    have e2 : log ((b : ℂ) + ((0 : ℝ) : ℂ) * I - 1) = (Real.log (1 - b) : ℂ) + Real.pi * I := by
      have : (b : ℂ) + ((0 : ℝ) : ℂ) * I - 1 = ((b - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.log, arg_ofReal_of_neg (by linarith)]
      congr 2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring_nf
    simp only [hA]
    rw [e1, e2]; simp
  set J := ∫ t in Ioi (0 : ℝ), f t with hJdef
  have hJv : J = I * A 0 := by
    have : I * J = -A 0 := by rw [hJ]; ring
    have h2 : J = -I * (I * J) := by
      rw [← mul_assoc]; simp
    rw [h2, this]; ring
  -- the negative half-line by conjugation
  have hneg : ∫ t in Iic (0 : ℝ), f t = conj J := by
    have hc := integral_comp_neg_Ioi (c := (0 : ℝ)) f
    rw [neg_zero] at hc
    rw [← hc, ← integral_conj]
    refine setIntegral_congr_ae measurableSet_Ioi (Eventually.of_forall (fun t ht => ?_))
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [hf]
    have c1 : (b : ℂ) + ((-t : ℝ) : ℂ) * I = conj ((b : ℂ) + t * I) := by
      apply Complex.ext <;> simp
    have c2 : conj ((b : ℂ) + t * I) - 1 = conj ((b : ℂ) + t * I - 1) := by
      simp
    rw [c1, c2, log_conj _ (mem_slitPlane_iff_arg.1 (line_mem_slitPlane ht0)).1,
      log_conj _ (mem_slitPlane_iff_arg.1 (line_sub_one_mem_slitPlane ht0)).1]
    simp [map_div₀]
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn, hneg, ← hJdef, hJv, hA0]
  apply Complex.ext <;> simp <;> field_simp <;> ring

end ZetaLog

end

section
open Complex MeasureTheory Filter Topology Set ComplexConjugate

namespace ZetaLog

/-- Half-line integral of an even integrable function. -/
lemma half_line_of_even {g : ℝ → ℝ} (hg : Integrable g) (heven : ∀ t, g (-t) = g t) :
    ∫ t in Ioi (0 : ℝ), g t = (1 / 2) * ∫ t, g t := by
  have h1 := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hg.integrableOn hg.integrableOn
  have h2 := integral_comp_neg_Ioi (c := (0 : ℝ)) g
  rw [neg_zero] at h2
  have h3 : ∫ x in Ioi (0 : ℝ), g (-x) = ∫ x in Ioi (0 : ℝ), g x := by
    congr 1; funext x; exact heven x
  rw [← h1, ← h2, h3]; ring

/-- `∫ β / ((β²+t²)(a²+t²)) dt = π / (a (a+β))`, from the Poisson formula. -/
lemma integral_rational {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    Integrable (fun t : ℝ => β / ((β ^ 2 + t ^ 2) * (a ^ 2 + t ^ 2))) ∧
    ∫ t : ℝ, β / ((β ^ 2 + t ^ 2) * (a ^ 2 + t ^ 2)) = Real.pi / (a * (a + β)) := by
  set Ψ : ℂ → ℂ := fun s => 1 / (s + β) with hΨ
  have hne : ∀ s : ℂ, (0 : ℝ) ≤ s.re → s + β ≠ 0 := by
    intro s hs h; have := congrArg Complex.re h; simp at this; linarith
  have hd : DifferentiableOn ℂ Ψ {s : ℂ | (0 : ℝ) ≤ s.re} := by
    intro s hs
    exact (DifferentiableAt.div (differentiableAt_const (1 : ℂ))
      (differentiableAt_id.add_const (β : ℂ)) (hne s hs)).differentiableWithinAt
  have hB : ∀ s : ℂ, (0 : ℝ) ≤ s.re → ‖Ψ s‖ ≤ (1 / β) * (1 + ‖s‖) ^ (0 : ℝ) := by
    intro s hs
    rw [Real.rpow_zero, mul_one, hΨ, norm_div, norm_one]
    apply one_div_le_one_div_of_le hβ
    have := Complex.re_le_norm (s + β); simp at this; linarith
  obtain ⟨hint, hval⟩ := Contour.poisson (F := Ψ) (b := 0) le_rfl (by norm_num) hd hB
    (α := a) (y := 0) ha
  have hre : ∀ t : ℝ, (Ψ (((0 : ℝ) : ℂ) + t * I) / (((a ^ 2 + (t - 0) ^ 2 : ℝ)) : ℂ)).re =
      β / ((β ^ 2 + t ^ 2) * (a ^ 2 + t ^ 2)) := by
    intro t
    simp only [hΨ]
    rw [show (((0 : ℝ) : ℂ) + t * I + β) = ((β : ℝ) : ℂ) + t * I by push_cast; ring,
      Complex.div_ofReal_re, one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
      add_im, mul_im, mul_one, zero_add, add_zero]
    have h1 : 0 < β ^ 2 + t ^ 2 := by positivity
    have h2 : 0 < a ^ 2 + t ^ 2 := by positivity
    rw [show β * β + t * t = β ^ 2 + t ^ 2 by ring, div_div]
  have hint' := hint.re
  refine ⟨hint'.congr (Eventually.of_forall hre), ?_⟩
  have := congrArg Complex.re hval
  have hI := integral_re hint
  simp only [RCLike.re_to_complex, hre] at hI
  rw [← hI] at this
  rw [this]
  simp only [hΨ]
  have : ((((0 : ℝ) + a : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I + β) = ((a + β : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp

/-- The `F`-part of the argument integral. -/
theorem F_part (hRH : RiemannHypothesis) {F : ℂ → ℂ} (hF : IsLogG0 F) {b a : ℝ} (hb : 1 / 2 < b)
    (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t * (F ((b : ℂ) + t * I)).im / (a ^ 2 + t ^ 2) ^ 2) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), t * (F ((b : ℂ) + t * I)).im / (a ^ 2 + t ^ 2) ^ 2 =
      Real.pi / (4 * a) * (deriv F (((b + a : ℝ) : ℂ))).re := by
  obtain ⟨C, hC⟩ := F_growth hRH hF hb
  have hFd : DifferentiableOn ℂ F {s : ℂ | b ≤ s.re} := by
    intro s hs
    have hmem : s ∈ U := by show 1 / 2 < s.re; have : b ≤ s.re := hs; linarith
    exact (hF.hasDeriv s hmem).differentiableAt.differentiableWithinAt
  obtain ⟨hint, hval⟩ := Contour.poisson_deriv (F := F) (b := b) (C := C) (r := 1 / 2)
    (by norm_num) (by norm_num) hFd hC (α := a) (y := 0) ha
  set g : ℝ → ℝ := fun t => t * (F ((b : ℂ) + t * I)).im / (a ^ 2 + t ^ 2) ^ 2 with hg
  have him : ∀ t : ℝ, (F ((b : ℂ) + t * I) * ((((t - 0) / (a ^ 2 + (t - 0) ^ 2) ^ 2 : ℝ)) : ℂ)).im =
      g t := by
    intro t
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
    simp only [hg, sub_zero]; ring
  have hgint : Integrable g := hint.im.congr (Eventually.of_forall him)
  have hgval : ∫ t, g t = Real.pi / (2 * a) * (deriv F (((b + a : ℝ) : ℂ))).re := by
    have := congrArg Complex.im hval
    have hI := integral_im hint
    simp only [RCLike.im_to_complex, him] at hI
    rw [← hI] at this
    rw [this]
    have e : ((b + a : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = ((b + a : ℝ) : ℂ) := by simp
    rw [e]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have heven : ∀ t, g (-t) = g t := by
    intro t
    simp only [hg]
    have hmem : (b : ℂ) + t * I ∈ U := by show 1 / 2 < ((b : ℂ) + t * I).re; simp; linarith
    have hc : (b : ℂ) + ((-t : ℝ) : ℂ) * I = conj ((b : ℂ) + t * I) := by
      apply Complex.ext <;> simp
    rw [hc, hF.conj_eq _ hmem, Complex.conj_im]
    ring
  refine ⟨hgint.integrableOn, ?_⟩
  rw [half_line_of_even hgint heven, hgval]
  ring

end ZetaLog

end

section
open Complex MeasureTheory Filter Topology Set ComplexConjugate

namespace ZetaLog

lemma arg_re_pos {z : ℂ} (hz : 0 < z.re) : arg z = Real.arctan (z.im / z.re) := by
  have h1 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  rw [← Complex.tan_arg, Real.arctan_tan (by linarith [neg_abs_le (arg z)])
    (by linarith [le_abs_self (arg z)])]

lemma im_L_eq {b t : ℝ} (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)).im =
      Real.arctan (t / b) + Real.arctan (t / (1 - b)) - Real.pi := by
  rw [sub_im, log_im, log_im]
  have e1 : arg ((b : ℂ) + t * I) = Real.arctan (t / b) := by
    rw [arg_re_pos (by simpa using hb)]; simp
  have hx : ((((1 - b : ℝ) : ℂ) - t * I)).im < 0 := by simp; linarith
  have e2 : (b : ℂ) + t * I - 1 = -(((1 - b : ℝ) : ℂ) - t * I) := by push_cast; ring
  have e3 : arg (((1 - b : ℝ) : ℂ) - t * I) = Real.arctan (-t / (1 - b)) := by
    rw [arg_re_pos (by simp; linarith)]; simp
  rw [e1, e2, arg_neg_eq_arg_add_pi_of_im_neg hx, e3, neg_div, Real.arctan_neg]
  ring

/-- The `L`-part of the argument integral. -/
theorem L_part {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) :
    IntegrableOn (fun t : ℝ => t * (log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)).im /
      (a ^ 2 + t ^ 2) ^ 2) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), t * (log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)).im /
      (a ^ 2 + t ^ 2) ^ 2 =
      -(Real.pi / (2 * a ^ 2)) + Real.pi / (4 * a) * (1 / (a + b) + 1 / (a + (1 - b))) := by
  set α := 1 - b with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  set u : ℝ → ℝ := fun t => Real.arctan (t / b) + Real.arctan (t / α) - Real.pi with hu
  set u' : ℝ → ℝ := fun t => b / (b ^ 2 + t ^ 2) + α / (α ^ 2 + t ^ 2) with hu'
  set v : ℝ → ℝ := fun t => -(1 / (2 * (a ^ 2 + t ^ 2))) with hv
  set v' : ℝ → ℝ := fun t => t / (a ^ 2 + t ^ 2) ^ 2 with hv'
  have hud : ∀ x : ℝ, HasDerivAt u (u' x) x := by
    intro x
    have h1 := (Contour.hasDerivAt_arctan_div hb x).const_mul b
    have h2 := (Contour.hasDerivAt_arctan_div hα0 x).const_mul α
    refine ((h1.add h2).sub_const Real.pi).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · refine Eventually.of_forall (fun y => ?_)
      simp only [hu, Pi.add_apply]; field_simp
    · simp only [hu']; ring
  have hvd : ∀ x : ℝ, HasDerivAt v (v' x) x := by
    intro x
    have hp : 0 < a ^ 2 + x ^ 2 := by positivity
    have h := ((((hasDerivAt_id x).pow 2).const_add (a ^ 2)).const_mul 2).inv
      (by positivity : (2 * (a ^ 2 + id x ^ 2)) ≠ 0)
    refine h.neg.congr_of_eventuallyEq (Eventually.of_forall (fun y => ?_)) |>.congr_deriv ?_
    · simp [hv]
    · simp only [hv', id_eq, Pi.pow_apply]; field_simp; ring
  have hubd : ∀ t, |u t| ≤ 2 * Real.pi := by
    intro t
    have := Real.arctan_lt_pi_div_two (t / b); have := Real.neg_pi_div_two_lt_arctan (t / b)
    have := Real.arctan_lt_pi_div_two (t / α); have := Real.neg_pi_div_two_lt_arctan (t / α)
    have := Real.pi_pos
    rw [abs_le]; constructor <;> simp only [hu] <;> linarith
  have hucont : Continuous u := continuous_iff_continuousAt.2 (fun x => (hud x).continuousAt)
  have huv' : Integrable (fun t => u t * v' t) := by
    refine (Contour.integrable_odd_sq ha).bdd_mul (c := 2 * Real.pi) hucont.aestronglyMeasurable
      (Eventually.of_forall (fun t => ?_))
    rw [Real.norm_eq_abs]; exact hubd t
  obtain ⟨hr1, hr1v⟩ := integral_rational ha hb
  obtain ⟨hr2, hr2v⟩ := integral_rational ha hα0
  have hu'v_eq : (fun t => u' t * v t) = fun t => -(1 / 2) *
      (b / ((b ^ 2 + t ^ 2) * (a ^ 2 + t ^ 2)) + α / ((α ^ 2 + t ^ 2) * (a ^ 2 + t ^ 2))) := by
    funext t
    have h1 : 0 < b ^ 2 + t ^ 2 := by positivity
    have h2 : 0 < α ^ 2 + t ^ 2 := by positivity
    have h3 : 0 < a ^ 2 + t ^ 2 := by positivity
    simp only [hu', hv]; field_simp
  have hu'v : Integrable (fun t => u' t * v t) := by
    rw [hu'v_eq]; exact (hr1.add hr2).const_mul _
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 (u 0 * v 0)) :=
    ((hucont.mul (continuous_iff_continuousAt.2 (fun x => (hvd x).continuousAt))).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hinf : Tendsto (u * v) atTop (𝓝 0) := by
    have hv0 : Tendsto v atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => 2 * (a ^ 2 + t ^ 2)) atTop atTop := by
        refine Tendsto.const_mul_atTop (by norm_num) ?_
        exact tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num))
      have := (tendsto_inv_atTop_zero.comp this).neg
      rw [neg_zero] at this
      refine this.congr (fun t => ?_); simp [hv]
    have hb' : ∀ t, ‖u t‖ ≤ 2 * Real.pi := fun t => by rw [Real.norm_eq_abs]; exact hubd t
    rw [tendsto_zero_iff_norm_tendsto_zero] at hv0 ⊢
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) (by simpa using hv0.const_mul (2 * Real.pi))
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb' t) (norm_nonneg _)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (fun x _ => hud x) (fun x _ => hvd x)
    huv'.integrableOn hu'v.integrableOn hzero hinf
  -- identify the integrand on `Ioi 0`
  have hcongr : EqOn (fun t : ℝ => t * (log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)).im /
      (a ^ 2 + t ^ 2) ^ 2) (fun t => u t * v' t) (Ioi 0) := by
    intro t ht
    simp only [hu, hv']
    rw [im_L_eq hb hb1 ht]; ring
  refine ⟨(huv'.integrableOn).congr_fun hcongr.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hibp]
  have he1 := half_line_of_even hr1 (fun t => by ring)
  have he2 := half_line_of_even hr2 (fun t => by ring)
  have : ∫ t in Ioi (0 : ℝ), u' t * v t = -(1 / 2) * ((∫ t in Ioi (0 : ℝ),
      b / ((b ^ 2 + t ^ 2) * (a ^ 2 + t ^ 2))) + ∫ t in Ioi (0 : ℝ),
      α / ((α ^ 2 + t ^ 2) * (a ^ 2 + t ^ 2))) := by
    rw [hu'v_eq, integral_const_mul, integral_add hr1.integrableOn hr2.integrableOn]
  rw [this, he1, he2, hr1v, hr2v]
  simp only [hu, hv]
  rw [show (0 : ℝ) / b = 0 by simp, show (0 : ℝ) / α = 0 by simp, Real.arctan_zero]
  have := Real.pi_pos
  field_simp
  ring

end ZetaLog

end

section
open Complex MeasureTheory Filter Topology Set ComplexConjugate

namespace ZetaLog

/-- Argument integral for `1/2 < b < 1`, in terms of `F'`. -/
theorem arg_formula (hRH : RiemannHypothesis) {F : ℂ → ℂ} (hF : IsLogG0 F) {a b : ℝ}
    (hb : 1 / 2 < b) (hb1 : b < 1) (ha : 0 < a) :
    let h (b t : ℝ) : ℂ := -(∫ u in Set.Ioi b, deriv riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I) /
      riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I))
    IntegrableOn (fun t : ℝ => t * (h b t).im / (a ^ 2 + t ^ 2) ^ 2) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), t * (h b t).im / (a ^ 2 + t ^ 2) ^ 2 =
      Real.pi / (4 * a) * (deriv F (((b + a : ℝ) : ℂ))).re +
      (-(Real.pi / (2 * a ^ 2)) + Real.pi / (4 * a) * (1 / (a + b) + 1 / (a + (1 - b)))) := by
  intro h
  obtain ⟨hF1, hF1v⟩ := F_part hRH hF hb ha
  obtain ⟨hL1, hL1v⟩ := L_part ha (by linarith : (0 : ℝ) < b) hb1
  have hcongr : EqOn (fun t : ℝ => t * (h b t).im / (a ^ 2 + t ^ 2) ^ 2)
      (fun t => t * (F ((b : ℂ) + t * I)).im / (a ^ 2 + t ^ 2) ^ 2 +
        t * (log ((b : ℂ) + t * I) - log ((b : ℂ) + t * I - 1)).im / (a ^ 2 + t ^ 2) ^ 2)
      (Ioi 0) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [h]
    rw [h_eq hRH hF hb ht0]
    simp only [sub_im, add_im]
    ring
  refine ⟨(hF1.add hL1).congr_fun hcongr.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_add hF1 hL1, hF1v, hL1v]

theorem sbmArgument_of_RH (hRH : RiemannHypothesis) :
    let h (b t : ℝ) : ℂ := -(∫ u in Set.Ioi b, deriv riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I) / riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I))
    ∀ b : ℝ, 1/2 < b → b < 1 →
      let f (t : ℝ) := t*(h b t).im/((1-b)^2+t^2)^2
      MeasureTheory.IntegrableOn f (Set.Ioi 0) ∧ (∫ t in Set.Ioi (0 : ℝ), f t) =
      Real.pi*Real.eulerMascheroniConstant/(4*(1-b)) - 3*Real.pi/(8*(1-b)^2) := by
  intro h b hb hb1 f
  obtain ⟨F, hF⟩ := exists_logG0 hRH
  have hα : 0 < 1 - b := by linarith
  obtain ⟨h1, h2⟩ := arg_formula hRH hF hb hb1 hα
  refine ⟨h1, ?_⟩
  show ∫ t in Ioi (0 : ℝ), t * (h b t).im / ((1 - b) ^ 2 + t ^ 2) ^ 2 = _
  rw [h2]
  have e : (((b + (1 - b) : ℝ)) : ℂ) = 1 := by push_cast; ring
  have hmem : (1 : ℂ) ∈ U := by show (1 : ℝ) / 2 < (1 : ℂ).re; norm_num
  rw [e, (hF.hasDeriv 1 hmem).deriv, deriv_G0_one, G0_one, div_one, sub_re, ofReal_re, one_re,
    show (1 - b) + b = 1 by ring, show (1 - b) + (1 - b) = 2 * (1 - b) by ring]
  field_simp
  ring

/-- `sbmArgumentParameter` in the range `1/2 < b`. -/
theorem argParam_open (hRH : RiemannHypothesis) {a b : ℝ} (ha : 0 < a) (hb : 1 / 2 < b)
    (hb1 : b < 1) (hab : a + b ≠ 1) :
    let h (b t : ℝ) : ℂ := -(∫ u in Set.Ioi b, deriv riemannZeta ((u : ℂ)+(t : ℂ)*Complex.I) / riemannZeta ((u : ℂ)+(t : ℂ)*Complex.I))
    let f (t : ℝ) := t*(h b t).im/(a^2+t^2)^2
    MeasureTheory.IntegrableOn f (Set.Ioi 0) ∧ (∫ t in Set.Ioi (0 : ℝ), f t) =
      Real.pi/(4*a)*(deriv riemannZeta ((a+b : ℝ) : ℂ) / riemannZeta ((a+b : ℝ) : ℂ)).re +
      Real.pi/2*(1/(a^2-(1-b)^2) - 1/a^2) := by
  intro h f
  obtain ⟨F, hF⟩ := exists_logG0 hRH
  obtain ⟨h1, h2⟩ := arg_formula hRH hF hb hb1 ha
  refine ⟨h1, ?_⟩
  show ∫ t in Ioi (0 : ℝ), t * (h b t).im / (a ^ 2 + t ^ 2) ^ 2 = _
  rw [h2]
  have hmem : (((b + a : ℝ)) : ℂ) ∈ U := by
    show (1 : ℝ) / 2 < (((b + a : ℝ)) : ℂ).re; rw [ofReal_re]; linarith
  have hs1 : (((b + a : ℝ)) : ℂ) ≠ 1 := by
    intro e; apply hab; have := congrArg Complex.re e; simp at this; linarith
  rw [deriv_F_eq hRH hF hmem hs1, show b + a = a + b by ring]
  have e1 : (1 : ℂ) / (((a + b : ℝ) : ℂ) - 1) = (((1 / (a + b - 1)) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 : ℂ) / (((a + b : ℝ) : ℂ)) = (((1 / (a + b)) : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, sub_re, add_re, ofReal_re, ofReal_re]
  have hab1 : a + b - 1 ≠ 0 := sub_ne_zero.2 hab
  have hab2 : 0 < a + (1 - b) := by linarith
  have hab3 : 0 < a + b := by linarith
  have hab4 : a ^ 2 - (1 - b) ^ 2 ≠ 0 := by
    rw [show a ^ 2 - (1 - b) ^ 2 = (a + b - 1) * (a + (1 - b)) by ring]
    exact mul_ne_zero hab1 hab2.ne'
  field_simp
  ring

end ZetaLog

end

section
theorem solution :
    let h (b t : ℝ) : ℂ := -(∫ u in Set.Ioi b, deriv riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I) / riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I))
    ∀ b : ℝ, 1/2 < b → b < 1 →
      let f (t : ℝ) := t*(h b t).im/((1-b)^2+t^2)^2
      MeasureTheory.IntegrableOn f (Set.Ioi 0) ∧ (∫ t in Set.Ioi (0 : ℝ), f t) =
      Real.pi*Real.eulerMascheroniConstant/(4*(1-b)) - 3*Real.pi/(8*(1-b)^2) :=
  ZetaLog.sbmArgument_of_RH riemann_hypothesis

end
