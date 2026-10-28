-- Prove2me | solution 1 for EthierKurtz.berry_esseen_bounded_independent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:37:03.245241+00:00
-- url     : https://prove2.me/submissions/51f5a18e-0d4e-4d88-b705-f856b994cca3

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section P99Hyps
section X19_Mills

/-! Gaussian toolkit for 99bcb804 (KMT): standard normal density, cdf, Mills-ratio bounds. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace P99bcb804

/-- Standard normal density. -/
noncomputable def phi (t : ℝ) : ℝ := (√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2))

lemma phi_pos (t : ℝ) : 0 < phi t := by
  unfold phi; positivity

lemma gaussianPDFReal_std (t : ℝ) : gaussianPDFReal 0 1 t = phi t := by
  simp [gaussianPDFReal_def, phi, neg_div]

lemma hasDerivAt_phi (t : ℝ) : HasDerivAt phi (-t * phi t) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 2)) (-t) t := by
    exact ((hasDerivAt_pow 2 t).div_const 2).neg.congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (√(2 * π))⁻¹
  show HasDerivAt (fun t => (√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2)))
    (-t * ((√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2)))) t
  exact h2.congr_deriv (by ring)

lemma continuous_phi : Continuous phi := by
  unfold phi; fun_prop

lemma tendsto_phi_atTop : Tendsto phi atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => -(t ^ 2 / 2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos)
  have := (Real.tendsto_exp_atBot.comp h).const_mul (√(2 * π))⁻¹
  rw [mul_zero] at this
  exact this

lemma integrable_phi : Integrable phi := by
  have := integrable_gaussianPDFReal 0 1
  simpa [funext gaussianPDFReal_std] using this

/-- Standard normal cdf as an integral of the density. -/
lemma cdf_std_eq (x : ℝ) : cdf (gaussianReal 0 1) x = ∫ t in Iic x, phi t := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      (fun t _ => gaussianPDFReal_nonneg _ _ t))]
  simp [gaussianPDFReal_std]

lemma integral_phi : ∫ t, phi t = 1 := by
  have := integral_gaussianPDFReal_eq_one 0 (v := 1) one_ne_zero
  simpa [funext gaussianPDFReal_std] using this

/-- Upper tail of the standard normal. -/
lemma one_sub_cdf_std (x : ℝ) : 1 - cdf (gaussianReal 0 1) x = ∫ t in Ioi x, phi t := by
  rw [cdf_std_eq, ← integral_phi, ← integral_add_compl (measurableSet_Iic (a := x)) integrable_phi,
    compl_Iic]
  ring

/-- `∫_x^∞ t φ(t) dt = φ(x)` for `x ≥ 0`, with integrability. -/
lemma integral_Ioi_mul_phi {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t => t * phi t) (Ioi x) ∧ ∫ t in Ioi x, t * phi t = phi x := by
  have hd : ∀ t ∈ Ioi x, HasDerivAt (fun t => -phi t) (t * phi t) t := by
    intro t _
    exact (hasDerivAt_phi t).neg.congr_deriv (by ring)
  have hc : ContinuousWithinAt (fun t => -phi t) (Ici x) x :=
    (continuous_phi.neg).continuousAt.continuousWithinAt
  have hpos : ∀ t ∈ Ioi x, 0 ≤ t * phi t := fun t ht =>
    mul_nonneg (hx.trans (le_of_lt ht)) (phi_pos t).le
  have hlim : Tendsto (fun t => -phi t) atTop (𝓝 0) := by
    simpa using tendsto_phi_atTop.neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc hd hpos hlim]
  ring

/-- Mills ratio, upper bound: `1 - Φ(x) ≤ φ(x)/x` for `x > 0`. -/
lemma mills_upper {x : ℝ} (hx : 0 < x) : 1 - cdf (gaussianReal 0 1) x ≤ phi x / x := by
  obtain ⟨hint, heq⟩ := integral_Ioi_mul_phi hx.le
  rw [one_sub_cdf_std, le_div_iff₀ hx, ← heq, ← integral_mul_const]
  refine setIntegral_mono_on (integrable_phi.integrableOn.mul_const x) hint measurableSet_Ioi
    (fun t ht => ?_)
  have : x ≤ t := le_of_lt ht
  nlinarith [phi_pos t]

lemma phi_neg (t : ℝ) : phi (-t) = phi t := by
  simp [phi]

/-- The standard normal cdf has derivative `φ`. -/
lemma hasDerivAt_cdf_std (x : ℝ) :
    HasDerivAt (fun y => cdf (gaussianReal 0 1) y) (phi x) x := by
  have e : (fun y => cdf (gaussianReal 0 1) y)
      = fun y => (∫ t in Iic 0, phi t) + ∫ t in (0 : ℝ)..y, phi t := by
    funext y
    rw [cdf_std_eq, ← intervalIntegral.integral_Iic_sub_Iic integrable_phi.integrableOn
      integrable_phi.integrableOn]
    ring
  rw [e]
  exact ((continuous_phi.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

/-- Symmetry: `Φ(-x) = 1 - Φ(x)`. -/
lemma cdf_std_neg (x : ℝ) : cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  rw [cdf_std_eq, one_sub_cdf_std]
  have : ∫ t in Iic (-x), phi t = ∫ t in Iic (-x), phi (-t) := by
    simp_rw [phi_neg]
  rw [this, integral_comp_neg_Iic, neg_neg]

/-- Lower-tail Mills bound: `Φ(x) ≤ φ(x)/(-x)` for `x < 0`. -/
lemma mills_upper_neg {x : ℝ} (hx : x < 0) : cdf (gaussianReal 0 1) x ≤ phi x / (-x) := by
  have h := mills_upper (x := -x) (by linarith)
  rw [cdf_std_neg, phi_neg] at h
  linarith

/-! ### Stein solution for the indicator `1{w ≤ z}` (Chen–Goldstein–Shao, Lemma 2.3) -/

/-- Standard normal cdf as a real function. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- `Φ/φ` (lower Mills ratio). -/
noncomputable def Qm (w : ℝ) : ℝ := Phi w / phi w

/-- `(1-Φ)/φ` (upper Mills ratio). -/
noncomputable def Rm (w : ℝ) : ℝ := (1 - Phi w) / phi w

lemma Rm_eq_Qm_neg (w : ℝ) : Rm w = Qm (-w) := by
  simp only [Rm, Qm, Phi, cdf_std_neg, phi_neg]

lemma Qm_nonneg (w : ℝ) : 0 ≤ Qm w :=
  div_nonneg (cdf_nonneg _ _) (phi_pos w).le

lemma Rm_nonneg (w : ℝ) : 0 ≤ Rm w := by
  rw [Rm_eq_Qm_neg]; exact Qm_nonneg _

lemma hasDerivAt_Qm (w : ℝ) : HasDerivAt Qm (1 + w * Qm w) w := by
  have := (hasDerivAt_cdf_std w).div (hasDerivAt_phi w) (phi_pos w).ne'
  refine this.congr_deriv ?_
  have hp := (phi_pos w).ne'
  simp only [Qm, Phi]
  field_simp
  ring

/-- `-w Φ(w)/φ(w) ≤ 1` for `w < 0`. -/
lemma neg_mul_Qm_le {w : ℝ} (hw : w < 0) : -w * Qm w ≤ 1 := by
  have h := mills_upper_neg hw
  have hp := phi_pos w
  unfold Qm Phi
  rw [le_div_iff₀ (by linarith)] at h
  rw [mul_div_assoc', div_le_one hp]
  linarith

/-- `w (1-Φ(w))/φ(w) ≤ 1` for `w > 0`. -/
lemma mul_Rm_le {w : ℝ} (hw : 0 < w) : w * Rm w ≤ 1 := by
  rw [Rm_eq_Qm_neg]
  have := neg_mul_Qm_le (w := -w) (by linarith)
  simpa using this

lemma one_add_mul_Qm_nonneg (w : ℝ) : 0 ≤ 1 + w * Qm w := by
  rcases lt_or_ge w 0 with hw | hw
  · have := neg_mul_Qm_le hw; nlinarith
  · have := Qm_nonneg w; nlinarith

lemma Qm_monotone : Monotone Qm :=
  monotone_of_deriv_nonneg (fun w => (hasDerivAt_Qm w).differentiableAt)
    (fun w => by rw [(hasDerivAt_Qm w).deriv]; exact one_add_mul_Qm_nonneg w)

lemma Rm_antitone : Antitone Rm := by
  intro a b hab
  rw [Rm_eq_Qm_neg, Rm_eq_Qm_neg]
  exact Qm_monotone (by linarith)

lemma hasDerivAt_Rm (w : ℝ) : HasDerivAt Rm (w * Rm w - 1) w := by
  have h : Rm = fun w => Qm (-w) := funext Rm_eq_Qm_neg
  rw [h]
  have := (hasDerivAt_Qm (-w)).comp w (hasDerivAt_neg w)
  refine this.congr_deriv ?_
  simp only
  ring

lemma Qm_zero_eq_Rm_zero : Rm 0 = Qm 0 := by
  rw [Rm_eq_Qm_neg, neg_zero]

lemma Phi_mul_Rm (z : ℝ) : Phi z * Rm z = (1 - Phi z) * Qm z := by
  simp only [Rm, Qm]; ring

/-! ## Child C (Tusnády quantile inequality), generic over the family of sum laws. -/

/-! ## Gaussian hazard `Hz = φ/(1-Φ)` and the two-sided log-tail Taylor bound (KMT 1976 II, (4.5)). -/

end P99bcb804

end X19_Mills

section X33_Stein

/-! Stein solution layer for 99bcb804 (copied from _be.lean). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace P99bcb804

/-- Stein solution `f_z` of `f' - w f = 1{w ≤ z} - Φ(z)`. -/
noncomputable def steinF (z w : ℝ) : ℝ :=
  if w ≤ z then (1 - Phi z) * Qm w else Phi z * Rm w

lemma Phi_nonneg (z : ℝ) : 0 ≤ Phi z := cdf_nonneg _ _
lemma Phi_le_one (z : ℝ) : Phi z ≤ 1 := cdf_le_one _ _

lemma steinF_nonneg (z w : ℝ) : 0 ≤ steinF z w := by
  unfold steinF
  have := Phi_le_one z
  split_ifs
  · exact mul_nonneg (by linarith) (Qm_nonneg w)
  · exact mul_nonneg (Phi_nonneg z) (Rm_nonneg w)

/-- The diagonal value `Φ(z)(1-Φ(z))/φ(z)` is at most `Q(0) = √(2π)/2`. -/
lemma diag_le (z : ℝ) : (1 - Phi z) * Qm z ≤ Qm 0 := by
  have h1 := Phi_le_one z
  have h0 := Phi_nonneg z
  rcases le_or_gt z 0 with hz | hz
  · have := Qm_monotone hz
    have := Qm_nonneg z
    nlinarith
  · rw [← Phi_mul_Rm, ← Qm_zero_eq_Rm_zero]
    have := Rm_antitone hz.le
    have := Rm_nonneg z
    nlinarith

lemma steinF_le (z w : ℝ) : steinF z w ≤ Qm 0 := by
  unfold steinF
  have h1 := Phi_le_one z
  have h0 := Phi_nonneg z
  split_ifs with hw
  · have := Qm_monotone hw
    have := diag_le z
    nlinarith
  · have := Rm_antitone (le_of_lt (not_le.mp hw))
    have := diag_le z
    rw [← Phi_mul_Rm] at this
    nlinarith

lemma abs_mul_steinF_le (z w : ℝ) : |w * steinF z w| ≤ 1 := by
  have hf := steinF_nonneg z w
  have h1 := Phi_le_one z
  have h0 := Phi_nonneg z
  rcases lt_or_ge w 0 with hw | hw
  · -- `w < 0`
    rw [abs_of_nonpos (by nlinarith)]
    unfold steinF
    split_ifs with hwz
    · have := neg_mul_Qm_le hw
      have := Qm_nonneg w
      nlinarith
    · -- z < w < 0: `Φ(z) R(w) ≤ Φ(w) R(w) = (1-Φ w) Q(w)`
      have hzw : z ≤ w := le_of_lt (not_le.mp hwz)
      have hPhi : Phi z ≤ Phi w := monotone_cdf _ hzw
      have hr := Rm_nonneg w
      have e := Phi_mul_Rm w
      have := neg_mul_Qm_le hw
      have := Qm_nonneg w
      have := Phi_nonneg w
      have := Phi_le_one w
      nlinarith [mul_le_mul_of_nonneg_right hPhi hr]
  · rw [abs_of_nonneg (by nlinarith)]
    unfold steinF
    split_ifs with hwz
    · -- 0 ≤ w ≤ z: `(1-Φ z) Q(w) ≤ (1-Φ w) Q(w) = Φ(w) R(w)`
      have hPhi : Phi w ≤ Phi z := monotone_cdf _ hwz
      have hq := Qm_nonneg w
      have e := Phi_mul_Rm w
      rcases eq_or_lt_of_le hw with h0w | h0w
      · rw [← h0w]; simp
      have := mul_Rm_le h0w
      have := Rm_nonneg w
      have := Phi_nonneg w
      have := Phi_le_one w
      nlinarith [mul_le_mul_of_nonneg_right hPhi hq]
    · have h0w : 0 < w ∨ w = 0 := by rcases eq_or_lt_of_le hw with h | h; right; exact h.symm; left; exact h
      rcases h0w with h0w | h0w
      · have := mul_Rm_le h0w
        have := Rm_nonneg w
        nlinarith
      · rw [h0w]; simp

lemma deriv1_bound {z w : ℝ} (hw : w ≤ z) :
    0 ≤ (1 - Phi z) * (1 + w * Qm w) ∧ (1 - Phi z) * (1 + w * Qm w) ≤ 1 := by
  have h1 := Phi_le_one z
  have hq := Qm_nonneg w
  have hn := one_add_mul_Qm_nonneg w
  refine ⟨mul_nonneg (by linarith) hn, ?_⟩
  rcases lt_or_ge w 0 with hw0 | hw0
  · have : w * Qm w ≤ 0 := by nlinarith
    have := Phi_nonneg z
    nlinarith
  · have hPhi : Phi w ≤ Phi z := monotone_cdf _ hw
    have e := Phi_mul_Rm w
    have hw1 := Phi_le_one w
    have hw2 := Phi_nonneg w
    have hR : w * Rm w ≤ 1 := by
      rcases eq_or_lt_of_le hw0 with h | h
      · rw [← h]; simp
      · exact mul_Rm_le h
    have hr := Rm_nonneg w
    -- (1-Φz)(1+wQ) ≤ (1-Φw)(1+wQ) = (1-Φw) + w Φw Rw ≤ 1
    have step : (1 - Phi z) * (1 + w * Qm w) ≤ (1 - Phi w) * (1 + w * Qm w) :=
      mul_le_mul_of_nonneg_right (by linarith) hn
    have : (1 - Phi w) * (1 + w * Qm w) = (1 - Phi w) + Phi w * (w * Rm w) := by
      have : (1 - Phi w) * (w * Qm w) = Phi w * (w * Rm w) := by
        rw [show (1 - Phi w) * (w * Qm w) = w * ((1 - Phi w) * Qm w) by ring, ← e]; ring
      linarith [this]
    nlinarith

lemma deriv2_bound {z w : ℝ} (hw : z ≤ w) :
    -1 ≤ Phi z * (w * Rm w - 1) ∧ Phi z * (w * Rm w - 1) ≤ 0 := by
  have h0 := Phi_nonneg z
  have h1 := Phi_le_one z
  have hr := Rm_nonneg w
  have hR : w * Rm w ≤ 1 := by
    rcases lt_or_ge 0 w with h | h
    · exact mul_Rm_le h
    · nlinarith
  refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)⟩
  rcases lt_or_ge w 0 with hw0 | hw0
  · have hPhi : Phi z ≤ Phi w := monotone_cdf _ hw
    have e := Phi_mul_Rm w
    have hq := neg_mul_Qm_le hw0
    have hq0 := Qm_nonneg w
    have hw1 := Phi_le_one w
    have hw2 := Phi_nonneg w
    have hpos : 0 ≤ 1 - w * Rm w := by nlinarith
    have step : Phi z * (1 - w * Rm w) ≤ Phi w * (1 - w * Rm w) :=
      mul_le_mul_of_nonneg_right hPhi hpos
    have : Phi w * (1 - w * Rm w) = Phi w + (-w * Qm w) * (1 - Phi w) := by
      have : Phi w * (w * Rm w) = w * ((1 - Phi w) * Qm w) := by rw [← e]; ring
      nlinarith [this]
    nlinarith [mul_le_mul_of_nonneg_right hq (show 0 ≤ 1 - Phi w by linarith)]
  · nlinarith [mul_nonneg hw0 hr]

lemma hasDerivAt_Qm_branch (z w : ℝ) :
    HasDerivAt (fun w => (1 - Phi z) * Qm w) ((1 - Phi z) * (1 + w * Qm w)) w :=
  (hasDerivAt_Qm w).const_mul _

lemma hasDerivAt_Rm_branch (z w : ℝ) :
    HasDerivAt (fun w => Phi z * Rm w) (Phi z * (w * Rm w - 1)) w :=
  (hasDerivAt_Rm w).const_mul _

lemma hasDerivAt_steinF_lt {z w : ℝ} (hw : w < z) :
    HasDerivAt (steinF z) ((1 - Phi z) * (1 + w * Qm w)) w := by
  have h : steinF z =ᶠ[𝓝 w] fun w => (1 - Phi z) * Qm w := by
    filter_upwards [Iio_mem_nhds hw] with v hv
    simp [steinF, le_of_lt (show v < z from hv)]
  exact (hasDerivAt_Qm_branch z w).congr_of_eventuallyEq h

/-- Stein equation off the jump point. -/
lemma stein_eq_lt {z w : ℝ} (hw : w < z) :
    (1 - Phi z) * (1 + w * Qm w) - w * steinF z w = 1 - Phi z := by
  simp only [steinF, if_pos hw.le]; ring

lemma stein_eq_gt {z w : ℝ} (hw : z < w) :
    Phi z * (w * Rm w - 1) - w * steinF z w = -Phi z := by
  simp only [steinF, if_neg (not_le.mpr hw)]; ring

/-- The Stein solution is 1-Lipschitz. -/
lemma steinF_lip (z a b : ℝ) : |steinF z a - steinF z b| ≤ |a - b| := by
  -- Lipschitz on each closed half-line, then glue at `z`.
  have L1 : ∀ a b, a ≤ z → b ≤ z → |steinF z a - steinF z b| ≤ |a - b| := by
    intro a b ha hb
    have hfa : steinF z a = (1 - Phi z) * Qm a := by simp [steinF, ha]
    have hfb : steinF z b = (1 - Phi z) * Qm b := by simp [steinF, hb]
    rw [hfa, hfb]
    have := (convex_Iic z).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun w => (1 - Phi z) * Qm w) (f' := fun w => (1 - Phi z) * (1 + w * Qm w)) (C := 1)
      (fun x _ => (hasDerivAt_Qm_branch z x).hasDerivWithinAt)
      (fun x hx => by
        obtain ⟨h0, h1⟩ := deriv1_bound (z := z) (w := x) hx
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
      hb ha
    simpa [Real.norm_eq_abs] using this
  have L2 : ∀ a b, z ≤ a → z ≤ b → |steinF z a - steinF z b| ≤ |a - b| := by
    intro a b ha hb
    have hfa : steinF z a = Phi z * Rm a := by
      rcases eq_or_lt_of_le ha with h | h
      · subst h; simp [steinF, Phi_mul_Rm]
      · simp [steinF, not_le.mpr h]
    have hfb : steinF z b = Phi z * Rm b := by
      rcases eq_or_lt_of_le hb with h | h
      · subst h; simp [steinF, Phi_mul_Rm]
      · simp [steinF, not_le.mpr h]
    rw [hfa, hfb]
    have := (convex_Ici z).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun w => Phi z * Rm w) (f' := fun w => Phi z * (w * Rm w - 1)) (C := 1)
      (fun x _ => (hasDerivAt_Rm_branch z x).hasDerivWithinAt)
      (fun x hx => by
        obtain ⟨h0, h1⟩ := deriv2_bound (z := z) (w := x) hx
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
      hb ha
    simpa [Real.norm_eq_abs] using this
  rcases le_total a z with ha | ha <;> rcases le_total b z with hb | hb
  · exact L1 a b ha hb
  · calc |steinF z a - steinF z b| ≤ |steinF z a - steinF z z| + |steinF z z - steinF z b| :=
          abs_sub_le _ _ _
      _ ≤ |a - z| + |z - b| := add_le_add (L1 a z ha le_rfl) (L2 z b le_rfl hb)
      _ = |a - b| := by
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          ring
  · calc |steinF z a - steinF z b| ≤ |steinF z a - steinF z z| + |steinF z z - steinF z b| :=
          abs_sub_le _ _ _
      _ ≤ |a - z| + |z - b| := add_le_add (L2 a z ha le_rfl) (L1 z b le_rfl hb)
      _ = |a - b| := by
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          ring
  · exact L2 a b ha hb

/-- The right derivative of the Stein solution (defined everywhere). -/
noncomputable def steinD (z w : ℝ) : ℝ :=
  if w < z then (1 - Phi z) * (1 + w * Qm w) else Phi z * (w * Rm w - 1)

lemma abs_steinD_le (z w : ℝ) : |steinD z w| ≤ 1 := by
  unfold steinD
  rw [abs_le]
  split_ifs with h
  · obtain ⟨h0, h1⟩ := deriv1_bound (z := z) (w := w) h.le; constructor <;> linarith
  · obtain ⟨h0, h1⟩ := deriv2_bound (z := z) (w := w) (not_lt.mp h); constructor <;> linarith

/-- Stein equation, everywhere: `f'₊(w) - w f(w) = 1{w < z} - Φ(z)`. -/
lemma stein_eq (z w : ℝ) :
    steinD z w - w * steinF z w = (if w < z then 1 else 0) - Phi z := by
  unfold steinD
  split_ifs with h
  · rw [stein_eq_lt h]
  · rcases eq_or_lt_of_le (not_lt.mp h) with h' | h'
    · subst h'
      simp only [steinF, le_refl, if_true]
      rw [← Phi_mul_Rm]; ring
    · rw [stein_eq_gt h']; ring

lemma steinF_eq_right {z w : ℝ} (hw : z ≤ w) : steinF z w = Phi z * Rm w := by
  rcases eq_or_lt_of_le hw with h | h
  · subst h; simp [steinF, Phi_mul_Rm]
  · simp [steinF, not_le.mpr h]

/-- Right derivative of the Stein solution. -/
lemma hasDerivWithinAt_steinF (z w : ℝ) :
    HasDerivWithinAt (steinF z) (steinD z w) (Ici w) w := by
  rcases lt_or_ge w z with h | h
  · rw [show steinD z w = (1 - Phi z) * (1 + w * Qm w) by simp [steinD, h]]
    exact (hasDerivAt_steinF_lt h).hasDerivWithinAt
  · rw [show steinD z w = Phi z * (w * Rm w - 1) by simp [steinD, not_lt.mpr h]]
    refine (hasDerivAt_Rm_branch z w).hasDerivWithinAt.congr (fun x hx => ?_) ?_
    · exact steinF_eq_right (h.trans hx)
    · exact steinF_eq_right h

lemma continuous_steinF (z : ℝ) : Continuous (steinF z) := by
  refine Metric.continuous_iff.mpr fun b ε hε => ⟨ε, hε, fun a hab => ?_⟩
  rw [Real.dist_eq] at hab ⊢
  exact lt_of_le_of_lt (steinF_lip z a b) hab

/-- CGS (2.10)-type bound: `|(w+u)f(w+u) - (w+v)f(w+v)| ≤ (|w| + √(2π)/2)(|u|+|v|)`. -/
lemma stein_mul_diff (z w u v : ℝ) :
    |(w + u) * steinF z (w + u) - (w + v) * steinF z (w + v)|
      ≤ (|w| + Qm 0) * (|u| + |v|) := by
  have e : (w + u) * steinF z (w + u) - (w + v) * steinF z (w + v)
      = w * (steinF z (w + u) - steinF z (w + v)) + u * steinF z (w + u)
        - v * steinF z (w + v) := by ring
  rw [e]
  have h1 : |w * (steinF z (w + u) - steinF z (w + v))| ≤ |w| * (|u| + |v|) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg w)
    have := steinF_lip z (w + u) (w + v)
    have : |w + u - (w + v)| ≤ |u| + |v| := by
      rw [show w + u - (w + v) = u - v by ring]; exact abs_sub _ _
    linarith
  have hf1 := steinF_nonneg z (w + u)
  have hf2 := steinF_nonneg z (w + v)
  have hb1 := steinF_le z (w + u)
  have hb2 := steinF_le z (w + v)
  have h2 : |u * steinF z (w + u)| ≤ |u| * Qm 0 := by
    rw [abs_mul, abs_of_nonneg hf1]; exact mul_le_mul_of_nonneg_left hb1 (abs_nonneg u)
  have h3 : |v * steinF z (w + v)| ≤ |v| * Qm 0 := by
    rw [abs_mul, abs_of_nonneg hf2]; exact mul_le_mul_of_nonneg_left hb2 (abs_nonneg v)
  calc |w * (steinF z (w + u) - steinF z (w + v)) + u * steinF z (w + u) - v * steinF z (w + v)|
      ≤ |w * (steinF z (w + u) - steinF z (w + v))| + |u * steinF z (w + u)|
          + |v * steinF z (w + v)| := by
        have := abs_sub (w * (steinF z (w + u) - steinF z (w + v)) + u * steinF z (w + u))
          (v * steinF z (w + v))
        have := abs_add_le (w * (steinF z (w + u) - steinF z (w + v))) (u * steinF z (w + u))
        linarith
    _ ≤ |w| * (|u| + |v|) + |u| * Qm 0 + |v| * Qm 0 := by linarith
    _ = (|w| + Qm 0) * (|u| + |v|) := by ring

lemma continuous_Qm : Continuous Qm :=
  continuous_iff_continuousAt.mpr fun w => (hasDerivAt_Qm w).continuousAt

lemma continuous_Rm : Continuous Rm :=
  continuous_iff_continuousAt.mpr fun w => (hasDerivAt_Rm w).continuousAt

lemma measurable_steinD (z : ℝ) : Measurable (steinD z) := by
  unfold steinD
  refine Measurable.ite (measurableSet_Iio (a := z)) ?_ ?_
  · exact (continuous_const.mul (continuous_const.add (continuous_id.mul continuous_Qm))).measurable
  · exact (continuous_const.mul ((continuous_id.mul continuous_Rm).sub continuous_const)).measurable

lemma intervalIntegrable_steinD (z a b : ℝ) : IntervalIntegrable (steinD z) volume a b := by
  refine IntegrableOn.intervalIntegrable ?_
  refine Measure.integrableOn_of_bounded (M := 1) (by simp [Real.volume_Icc, uIcc])
    (measurable_steinD z).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]; exact abs_steinD_le z x

/-- Fundamental theorem of calculus for the Stein solution. -/
lemma steinF_sub_eq_integral (z a b : ℝ) :
    steinF z b - steinF z a = ∫ t in a..b, steinD z t := by
  have key : ∀ a b : ℝ, a ≤ b → steinF z b - steinF z a = ∫ t in a..b, steinD z t := by
    intro a b hab
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
      (continuous_steinF z).continuousOn
      (fun x _ => (hasDerivWithinAt_steinF z x).mono Ioi_subset_Ici_self)
      (intervalIntegrable_steinD z a b)]
  rcases le_total a b with h | h
  · exact key a b h
  · rw [intervalIntegral.integral_symm, ← key b a h]; ring

lemma phi_le_half (t : ℝ) : phi t ≤ 1 / 2 := by
  unfold phi
  have h1 : (2 : ℝ) ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have h2 : (√(2 * π))⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h1
  have h3 : rexp (-(t ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have h4 : 0 ≤ (√(2 * π))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc (√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2)) ≤ (√(2 * π))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h3 h4
    _ ≤ 1 / 2 := by rw [mul_one]; exact h2

lemma Phi_sub_le {u v : ℝ} (h : v ≤ u) : Phi u - Phi v ≤ (u - v) / 2 := by
  have hd : ∀ x, HasDerivAt Phi (phi x) x := fun x => by
    show HasDerivAt (fun y => cdf (gaussianReal 0 1) y) _ _; exact hasDerivAt_cdf_std x
  have := image_sub_le_mul_sub_of_deriv_le (f := Phi) (C := 1 / 2)
    (fun x => (hd x).differentiableAt) (fun x => by rw [(hd x).deriv]; exact phi_le_half x) h
  linarith

lemma Qm_zero_le : Qm 0 ≤ 3 := by
  unfold Qm
  have hphi : phi 0 = (√(2 * π))⁻¹ := by simp [phi]
  rw [hphi, div_inv_eq_mul]
  have h1 : √(2 * π) ≤ 3 := by
    calc √(2 * π) ≤ √(3 ^ 2) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d2])
      _ = 3 := Real.sqrt_sq (by norm_num)
  have := mul_le_mul (Phi_le_one 0) h1 (Real.sqrt_nonneg _) (by norm_num)
  linarith

end P99bcb804

end X33_Stein

section X34_BdBE

/-! Berry–Esseen for independent, non-identically distributed, uniformly bounded summands
(Stein's method, bounded case, cf. Chen–Goldstein–Shao, Normal Approximation by Stein's Method,
§3.1): if `|ξ_i| ≤ δ ≤ 1`, `E ξ_i = 0`, `Σ E ξ_i² = 1`, then `|P(W < z) - Φ(z)| ≤ 7δ`. -/

open MeasureTheory ProbabilityTheory Real Set Finset

namespace P99bcb804

lemma steinD_lower (z δ w v : ℝ) (hv : |v - w| ≤ δ) :
    w * steinF z w + (if w < z - δ then 1 else 0) - Phi z - (|w| + 3) * δ ≤ steinD z v := by
  have e := stein_eq z v
  have hm := stein_mul_diff z w (v - w) 0
  rw [show w + (v - w) = v by ring, add_zero, abs_zero, add_zero] at hm
  have hq := Qm_zero_le
  have hq0 := Qm_nonneg 0
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hv
  have h1 : (|w| + Qm 0) * |v - w| ≤ (|w| + 3) * δ :=
    mul_le_mul (by linarith) hv (abs_nonneg _) (by positivity)
  have h2 : (if w < z - δ then (1:ℝ) else 0) ≤ (if v < z then 1 else 0) := by
    have := (abs_le.mp hv).2
    by_cases ha : w < z - δ
    · have hvz : v < z := by linarith
      simp [ha, hvz]
    · simp only [ha, if_false]; split_ifs <;> norm_num
  have := (abs_le.mp hm).1
  linarith

lemma steinD_upper (z δ w v : ℝ) (hv : |v - w| ≤ δ) :
    steinD z v ≤ w * steinF z w + (if w < z + δ then 1 else 0) - Phi z + (|w| + 3) * δ := by
  have e := stein_eq z v
  have hm := stein_mul_diff z w (v - w) 0
  rw [show w + (v - w) = v by ring, add_zero, abs_zero, add_zero] at hm
  have hq := Qm_zero_le
  have hq0 := Qm_nonneg 0
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hv
  have h1 : (|w| + Qm 0) * |v - w| ≤ (|w| + 3) * δ :=
    mul_le_mul (by linarith) hv (abs_nonneg _) (by positivity)
  have h2 : (if v < z then (1:ℝ) else 0) ≤ (if w < z + δ then 1 else 0) := by
    have := (abs_le.mp hv).1
    by_cases ha : v < z
    · have hwz : w < z + δ := by linarith
      simp [ha, hwz]
    · simp only [ha, if_false]; split_ifs <;> norm_num
  have := (abs_le.mp hm).2
  linarith

lemma mul_diff_lower (z δ w x L : ℝ) (hx : |x| ≤ δ)
    (hL : ∀ v, |v - w| ≤ δ → L ≤ steinD z v) :
    x ^ 2 * L ≤ x * (steinF z w - steinF z (w - x)) := by
  rw [steinF_sub_eq_integral z (w - x) w]
  have hx1 := (abs_le.mp hx).1
  have hx2 := (abs_le.mp hx).2
  rcases le_total 0 x with h | h
  · have hI := intervalIntegral.integral_mono_on (show w - x ≤ w by linarith)
      (intervalIntegrable_const (c := L)) (intervalIntegrable_steinD z (w - x) w)
      (fun t ht => hL t (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul, show w - (w - x) = x by ring] at hI
    nlinarith
  · have hI := intervalIntegral.integral_mono_on (show w ≤ w - x by linarith)
      (intervalIntegrable_const (c := L)) (intervalIntegrable_steinD z w (w - x))
      (fun t ht => hL t (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul, show w - x - w = -x by ring] at hI
    rw [intervalIntegral.integral_symm]
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr hI)]

lemma mul_diff_upper (z δ w x U : ℝ) (hx : |x| ≤ δ)
    (hU : ∀ v, |v - w| ≤ δ → steinD z v ≤ U) :
    x * (steinF z w - steinF z (w - x)) ≤ x ^ 2 * U := by
  rw [steinF_sub_eq_integral z (w - x) w]
  have hx1 := (abs_le.mp hx).1
  have hx2 := (abs_le.mp hx).2
  rcases le_total 0 x with h | h
  · have hI := intervalIntegral.integral_mono_on (show w - x ≤ w by linarith)
      (intervalIntegrable_steinD z (w - x) w) (intervalIntegrable_const (c := U))
      (fun t ht => hU t (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul, show w - (w - x) = x by ring] at hI
    nlinarith
  · have hI := intervalIntegral.integral_mono_on (show w ≤ w - x by linarith)
      (intervalIntegrable_steinD z w (w - x)) (intervalIntegrable_const (c := U))
      (fun t ht => hU t (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul, show w - x - w = -x by ring] at hI
    rw [intervalIntegral.integral_symm]
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr hI)]

lemma abs_ite_sub_Phi (p : Prop) [Decidable p] (z : ℝ) : |(if p then (1:ℝ) else 0) - Phi z| ≤ 1 := by
  have := Phi_nonneg z; have := Phi_le_one z
  rw [abs_le]; split_ifs <;> constructor <;> linarith

/-- Pointwise algebra: from `A ≥ Q (Lf - (|W|+3)δ)` with `|Lf| ≤ 2`, `Q ≥ 0`. -/
lemma alg_lower {A Q Lf W δ : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q) (hL : |Lf| ≤ 2)
    (h : Q * (Lf - (|W| + 3) * δ) ≤ A) :
    Lf - ((Q - 1) ^ 2 + δ ^ 2) / δ - δ * (Q ^ 2 + W ^ 2) / 2 - 3 * δ * Q ≤ A := by
  have h1 : 2 * |Q - 1| ≤ ((Q - 1) ^ 2 + δ ^ 2) / δ := by
    rw [le_div_iff₀ hδ]; nlinarith [sq_nonneg (|Q - 1| - δ), sq_abs (Q - 1)]
  have h2 : (Q - 1) * Lf ≥ -(2 * |Q - 1|) := by
    have := abs_mul (Q - 1) Lf
    have := neg_abs_le ((Q - 1) * Lf)
    nlinarith [abs_nonneg (Q - 1), abs_nonneg Lf]
  have h3 : Q * |W| ≤ (Q ^ 2 + W ^ 2) / 2 := by
    nlinarith [sq_nonneg (Q - |W|), sq_abs W]
  have h4 : δ * (Q * |W|) ≤ δ * ((Q ^ 2 + W ^ 2) / 2) := mul_le_mul_of_nonneg_left h3 hδ.le
  nlinarith

lemma alg_upper {A Q Uf W δ : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q) (hU : |Uf| ≤ 2)
    (h : A ≤ Q * (Uf + (|W| + 3) * δ)) :
    A ≤ Uf + ((Q - 1) ^ 2 + δ ^ 2) / δ + δ * (Q ^ 2 + W ^ 2) / 2 + 3 * δ * Q := by
  have h1 : 2 * |Q - 1| ≤ ((Q - 1) ^ 2 + δ ^ 2) / δ := by
    rw [le_div_iff₀ hδ]; nlinarith [sq_nonneg (|Q - 1| - δ), sq_abs (Q - 1)]
  have h2 : (Q - 1) * Uf ≤ 2 * |Q - 1| := by
    have := abs_mul (Q - 1) Uf
    have := le_abs_self ((Q - 1) * Uf)
    nlinarith [abs_nonneg (Q - 1), abs_nonneg Uf]
  have h3 : Q * |W| ≤ (Q ^ 2 + W ^ 2) / 2 := by
    nlinarith [sq_nonneg (Q - |W|), sq_abs W]
  have h4 : δ * (Q * |W|) ≤ δ * ((Q ^ 2 + W ^ 2) / 2) := mul_le_mul_of_nonneg_left h3 hδ.le
  nlinarith

lemma sq_bdd {a C : ℝ} (h : |a| ≤ C) : |a ^ 2| ≤ C ^ 2 := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg a) h 2

lemma Lf_bdd (z c w : ℝ) : |w * steinF z w + (if w < c then 1 else 0) - Phi z| ≤ 2 := by
  have h1 := abs_mul_steinF_le z w
  have h2 := abs_ite_sub_Phi (w < c) z
  rw [show w * steinF z w + (if w < c then 1 else 0) - Phi z
      = w * steinF z w + ((if w < c then 1 else 0) - Phi z) by ring]
  linarith [abs_add_le (w * steinF z w) ((if w < c then (1:ℝ) else 0) - Phi z)]

lemma split_sum {ι : Type} [Fintype ι] (z : ℝ) (x : ι → ℝ) :
    ∑ i, x i * (steinF z (∑ j, x j) - steinF z (∑ j, x j - x i))
      = (∑ j, x j) * steinF z (∑ j, x j) - ∑ i, x i * steinF z (∑ j, x j - x i) := by
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

lemma pt_lower {ι : Type} [Fintype ι] (z δ : ℝ) (hδ : 0 < δ) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ δ) :
    (if ∑ i, x i < z - δ then (1:ℝ) else 0) - ((1 / δ) * ((∑ i, x i ^ 2) - 1) ^ 2
      + (δ / 2) * (∑ i, x i ^ 2) ^ 2 + (δ / 2) * (∑ i, x i) ^ 2 + (3 * δ) * (∑ i, x i ^ 2) + δ)
      ≤ Phi z - ∑ i, x i * steinF z (∑ j, x j - x i) := by
  have hA : (∑ i, x i ^ 2) * ((∑ j, x j) * steinF z (∑ j, x j)
      + (if (∑ j, x j) < z - δ then 1 else 0) - Phi z - (|∑ j, x j| + 3) * δ)
      ≤ ∑ i, x i * (steinF z (∑ j, x j) - steinF z (∑ j, x j - x i)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      mul_diff_lower z δ _ (x i) _ (hx i) (fun v hv => steinD_lower z δ _ v hv)
  have hQ : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have := alg_lower hδ hQ (Lf_bdd z (z - δ) (∑ j, x j)) hA
  rw [split_sum] at this
  have e : (((∑ i, x i ^ 2) - 1) ^ 2 + δ ^ 2) / δ = (1 / δ) * ((∑ i, x i ^ 2) - 1) ^ 2 + δ := by
    field_simp
  rw [e] at this
  linarith

lemma pt_upper {ι : Type} [Fintype ι] (z δ : ℝ) (hδ : 0 < δ) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ δ) :
    Phi z - ∑ i, x i * steinF z (∑ j, x j - x i)
      ≤ (if ∑ i, x i < z + δ then (1:ℝ) else 0) + ((1 / δ) * ((∑ i, x i ^ 2) - 1) ^ 2
      + (δ / 2) * (∑ i, x i ^ 2) ^ 2 + (δ / 2) * (∑ i, x i) ^ 2 + (3 * δ) * (∑ i, x i ^ 2) + δ) := by
  have hA : ∑ i, x i * (steinF z (∑ j, x j) - steinF z (∑ j, x j - x i))
      ≤ (∑ i, x i ^ 2) * ((∑ j, x j) * steinF z (∑ j, x j)
      + (if (∑ j, x j) < z + δ then 1 else 0) - Phi z + (|∑ j, x j| + 3) * δ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      mul_diff_upper z δ _ (x i) _ (hx i) (fun v hv => steinD_upper z δ _ v hv)
  have hQ : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have := alg_upper hδ hQ (Lf_bdd z (z + δ) (∑ j, x j)) hA
  rw [split_sum] at this
  have e : (((∑ i, x i ^ 2) - 1) ^ 2 + δ ^ 2) / δ = (1 / δ) * ((∑ i, x i ^ 2) - 1) ^ 2 + δ := by
    field_simp
  rw [e] at this
  linarith

section Prob

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type} [Fintype ι] [DecidableEq ι]

lemma intB {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact h ω)

lemma prob_eq_integral {W : Ω → ℝ} (hW : Measurable W) (c : ℝ) :
    ∫ ω, (if W ω < c then (1:ℝ) else 0) ∂P = (P {ω | W ω < c}).toReal := by
  have hs : MeasurableSet {ω | W ω < c} := measurableSet_lt hW measurable_const
  have e : (fun ω => if W ω < c then (1:ℝ) else 0) = Set.indicator {ω | W ω < c} 1 := by
    funext ω; simp [Set.indicator_apply]
  rw [e, integral_indicator_one hs, measureReal_def]

omit [DecidableEq ι] in
lemma int_lin {a X1 X2 X3 X4 : Ω → ℝ} (ha : Integrable a P) (h1 : Integrable X1 P)
    (h2 : Integrable X2 P) (h3 : Integrable X3 P) (h4 : Integrable X4 P) (c1 c2 c3 c4 c : ℝ) :
    ∫ ω, (a ω - (c1 * X1 ω + c2 * X2 ω + c3 * X3 ω + c4 * X4 ω + c)) ∂P
      = (∫ ω, a ω ∂P) - (c1 * ∫ ω, X1 ω ∂P + c2 * ∫ ω, X2 ω ∂P + c3 * ∫ ω, X3 ω ∂P
          + c4 * ∫ ω, X4 ω ∂P + c) := by
  have i12 : Integrable (fun ω => c1 * X1 ω + c2 * X2 ω) P := (h1.const_mul c1).add (h2.const_mul c2)
  have i123 : Integrable (fun ω => c1 * X1 ω + c2 * X2 ω + c3 * X3 ω) P := i12.add (h3.const_mul c3)
  have i1234 : Integrable (fun ω => c1 * X1 ω + c2 * X2 ω + c3 * X3 ω + c4 * X4 ω) P :=
    i123.add (h4.const_mul c4)
  have i5 : Integrable (fun ω => c1 * X1 ω + c2 * X2 ω + c3 * X3 ω + c4 * X4 ω + c) P :=
    i1234.add (integrable_const c)
  rw [integral_sub ha i5, integral_add i1234 (integrable_const c), integral_add i123 (h4.const_mul c4),
    integral_add i12 (h3.const_mul c3), integral_add (h1.const_mul c1) (h2.const_mul c2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  simp

omit [DecidableEq ι] in
lemma int_lin' {a X1 X2 X3 X4 : Ω → ℝ} (ha : Integrable a P) (h1 : Integrable X1 P)
    (h2 : Integrable X2 P) (h3 : Integrable X3 P) (h4 : Integrable X4 P) (c1 c2 c3 c4 c : ℝ) :
    ∫ ω, (a ω + (c1 * X1 ω + c2 * X2 ω + c3 * X3 ω + c4 * X4 ω + c)) ∂P
      = (∫ ω, a ω ∂P) + (c1 * ∫ ω, X1 ω ∂P + c2 * ∫ ω, X2 ω ∂P + c3 * ∫ ω, X3 ω ∂P
          + c4 * ∫ ω, X4 ω ∂P + c) := by
  have i12 : Integrable (fun ω => c1 * X1 ω + c2 * X2 ω) P := (h1.const_mul c1).add (h2.const_mul c2)
  have i123 : Integrable (fun ω => c1 * X1 ω + c2 * X2 ω + c3 * X3 ω) P := i12.add (h3.const_mul c3)
  have i1234 : Integrable (fun ω => c1 * X1 ω + c2 * X2 ω + c3 * X3 ω + c4 * X4 ω) P :=
    i123.add (h4.const_mul c4)
  have i5 : Integrable (fun ω => c1 * X1 ω + c2 * X2 ω + c3 * X3 ω + c4 * X4 ω + c) P :=
    i1234.add (integrable_const c)
  rw [integral_add ha i5, integral_add i1234 (integrable_const c), integral_add i123 (h4.const_mul c4),
    integral_add i12 (h3.const_mul c3), integral_add (h1.const_mul c1) (h2.const_mul c2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  simp

variable (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P) (hmeas : ∀ i, Measurable (ξ i)) {δ : ℝ}
  (hδ : 0 < δ) (hb : ∀ i ω, |ξ i ω| ≤ δ) (h0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
  (h1 : ∑ i, ∫ ω, ξ i ω ^ 2 ∂P = 1)
include hind hmeas hδ hb h0 h1

lemma bdd_W (ω : Ω) : |∑ i, ξ i ω| ≤ Fintype.card ι * δ := by
  calc |∑ i, ξ i ω| ≤ ∑ i, |ξ i ω| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum fun i _ => hb i ω
    _ = Fintype.card ι * δ := by simp

lemma bdd_Q (ω : Ω) : |∑ i, ξ i ω ^ 2| ≤ Fintype.card ι * δ ^ 2 := by
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc ∑ i, ξ i ω ^ 2 ≤ ∑ _i : ι, δ ^ 2 := Finset.sum_le_sum fun i _ => by
        have := hb i ω; nlinarith [sq_abs (ξ i ω), abs_nonneg (ξ i ω)]
    _ = Fintype.card ι * δ ^ 2 := by simp

/-- Leave-one-out orthogonality `E[ξ_i g(W - ξ_i)] = 0`. -/
lemma loo_zero (g : ℝ → ℝ) (hg : Measurable g) (G : ℝ) (hG : ∀ w, |g w| ≤ G) (i : ι) :
    ∫ ω, ξ i ω * g (∑ j, ξ j ω - ξ i ω) ∂P = 0 := by
  have hind' : IndepFun (∑ j ∈ univ.erase i, ξ j) (ξ i) P :=
    hind.indepFun_finsetSum_of_notMem hmeas (Finset.notMem_erase i univ)
  have hc := (hind'.comp hg measurable_id).symm
  have e : ∀ ω, ∑ j, ξ j ω - ξ i ω = (∑ j ∈ univ.erase i, ξ j) ω := by
    intro ω
    rw [Finset.sum_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
  simp_rw [e]
  have hS : Measurable (∑ j ∈ univ.erase i, ξ j) := by
    rw [show (∑ j ∈ univ.erase i, ξ j) = fun ω => ∑ j ∈ univ.erase i, ξ j ω from by
      funext ω; simp [Finset.sum_apply]]
    exact Finset.measurable_sum _ fun j _ => hmeas j
  have := hc.integral_fun_mul_eq_mul_integral (hmeas i).aestronglyMeasurable
    (hg.comp hS).aestronglyMeasurable
  simp only [Function.comp, id] at this
  rw [this, h0 i, zero_mul]

lemma moments :
    ∫ ω, (∑ i, ξ i ω ^ 2) ∂P = 1 ∧ ∫ ω, (∑ i, ξ i ω) ^ 2 ∂P = 1 ∧
      ∫ ω, (∑ i, ξ i ω ^ 2) ^ 2 ∂P ≤ 1 + δ ^ 2 ∧
      ∫ ω, ((∑ i, ξ i ω ^ 2) - 1) ^ 2 ∂P ≤ δ ^ 2 := by
  have hmem : ∀ i, MemLp (ξ i) 2 P := fun i =>
    MemLp.of_bound (hmeas i).aestronglyMeasurable δ
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb i ω)
  have hsq : ∀ i, Measurable (fun ω => ξ i ω ^ 2) := fun i => (hmeas i).pow_const 2
  have hmem2 : ∀ i, MemLp (fun ω => ξ i ω ^ 2) 2 P := fun i =>
    MemLp.of_bound (hsq i).aestronglyMeasurable (δ ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := hb i ω; nlinarith [sq_abs (ξ i ω), abs_nonneg (ξ i ω)])
  have hint : ∀ i, Integrable (ξ i) P := fun i => (hmem i).integrable one_le_two
  have hint2 : ∀ i, Integrable (fun ω => ξ i ω ^ 2) P := fun i => (hmem2 i).integrable one_le_two
  have hEQ : ∫ ω, (∑ i, ξ i ω ^ 2) ∂P = 1 := by
    rw [integral_finsetSum _ fun i _ => hint2 i]; exact h1
  -- variance of W
  have hVW := IndepFun.variance_sum (μ := P) (s := univ) (fun i _ => hmem i)
    (fun i _ j _ hij => hind.indepFun hij)
  have eW : (∑ i ∈ univ, ξ i) = fun ω => ∑ i, ξ i ω := by funext ω; simp [Finset.sum_apply]
  rw [eW] at hVW
  have hmemW : MemLp (fun ω => ∑ i, ξ i ω) 2 P := by
    have := memLp_finsetSum' (s := univ) (fun i _ => hmem i)
    rwa [eW] at this
  rw [variance_eq_sub hmemW] at hVW
  have hEW : ∫ ω, ∑ i, ξ i ω ∂P = 0 := by
    rw [integral_finsetSum _ fun i _ => hint i]; simp [h0]
  have hvi : ∀ i, variance (ξ i) P = ∫ ω, ξ i ω ^ 2 ∂P := fun i => by
    rw [variance_eq_sub (hmem i)]; simp [h0 i]
  simp only [Pi.pow_apply, hEW] at hVW
  rw [Finset.sum_congr rfl fun i _ => hvi i, h1] at hVW
  have hW2 : ∫ ω, (∑ i, ξ i ω) ^ 2 ∂P = 1 := by linarith
  -- variance of Q
  have hVQ := IndepFun.variance_sum (μ := P) (s := univ) (X := fun i ω => ξ i ω ^ 2)
    (fun i _ => hmem2 i)
    (fun i _ j _ hij => (hind.indepFun hij).comp (measurable_id.pow_const 2)
      (measurable_id.pow_const 2))
  have eQ : (∑ i ∈ univ, fun ω => ξ i ω ^ 2) = fun ω => ∑ i, ξ i ω ^ 2 := by
    funext ω; simp [Finset.sum_apply]
  rw [eQ] at hVQ
  have hmemQ : MemLp (fun ω => ∑ i, ξ i ω ^ 2) 2 P := by
    have := memLp_finsetSum' (s := univ) (fun i _ => hmem2 i)
    rwa [eQ] at this
  have hVQ0 : variance (fun ω => ∑ i, ξ i ω ^ 2) P = ∫ ω, ((∑ i, ξ i ω ^ 2) - 1) ^ 2 ∂P := by
    rw [variance_eq_integral hmemQ.aestronglyMeasurable.aemeasurable]; simp only [hEQ]
  have hVQs := variance_eq_sub hmemQ
  simp only [Pi.pow_apply, hEQ] at hVQs
  have hvi2 : ∀ i, variance (fun ω => ξ i ω ^ 2) P ≤ δ ^ 2 * ∫ ω, ξ i ω ^ 2 ∂P := fun i => by
    rw [variance_eq_sub (hmem2 i)]
    simp only [Pi.pow_apply]
    have hle : ∫ ω, (ξ i ω ^ 2) ^ 2 ∂P ≤ ∫ ω, δ ^ 2 * ξ i ω ^ 2 ∂P := by
      refine integral_mono ((hmem2 i).integrable_sq) ((hint2 i).const_mul _) fun ω => ?_
      have := hb i ω
      have h4 : ξ i ω ^ 2 ≤ δ ^ 2 := by nlinarith [sq_abs (ξ i ω), abs_nonneg (ξ i ω)]
      simp only
      nlinarith [sq_nonneg (ξ i ω)]
    rw [integral_const_mul] at hle
    nlinarith [sq_nonneg (∫ ω, ξ i ω ^ 2 ∂P)]
  have hsumv : ∑ i, variance (fun ω => ξ i ω ^ 2) P ≤ δ ^ 2 := by
    calc ∑ i, variance (fun ω => ξ i ω ^ 2) P ≤ ∑ i, δ ^ 2 * ∫ ω, ξ i ω ^ 2 ∂P :=
          Finset.sum_le_sum fun i _ => hvi2 i
      _ = δ ^ 2 := by rw [← Finset.mul_sum, h1, mul_one]
  refine ⟨hEQ, hW2, by linarith, ?_⟩
  rw [← hVQ0, hVQ]; exact hsumv

/-- The integrability package and the leave-one-out mean of the Stein term. -/
lemma pieces (z : ℝ) (c : ℝ) :
    Integrable (fun ω => if ∑ i, ξ i ω < c then (1:ℝ) else 0) P ∧
    Integrable (fun ω => ((∑ i, ξ i ω ^ 2) - 1) ^ 2) P ∧
    Integrable (fun ω => (∑ i, ξ i ω ^ 2) ^ 2) P ∧
    Integrable (fun ω => (∑ i, ξ i ω) ^ 2) P ∧
    Integrable (fun ω => ∑ i, ξ i ω ^ 2) P ∧
    Integrable (fun ω => Phi z - ∑ i, ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) P ∧
    ∫ ω, (Phi z - ∑ i, ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) ∂P = Phi z := by
  have hWm : Measurable (fun ω => ∑ i, ξ i ω) := Finset.measurable_sum _ fun i _ => hmeas i
  have hQm : Measurable (fun ω => ∑ i, ξ i ω ^ 2) :=
    Finset.measurable_sum _ fun i _ => (hmeas i).pow_const 2
  have hW := bdd_W ξ hind hmeas hδ hb h0 h1
  have hQ := bdd_Q ξ hind hmeas hδ hb h0 h1
  have hfm := (continuous_steinF z).measurable
  have hf3 : ∀ w, |steinF z w| ≤ 3 := fun w => by
    rw [abs_of_nonneg (steinF_nonneg z w)]; exact (steinF_le z w).trans Qm_zero_le
  have hterm : ∀ i, Integrable (fun ω => ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) P := fun i =>
    intB ((hmeas i).mul (hfm.comp (hWm.sub (hmeas i)))) (δ * 3) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hb i ω) (hf3 _) (abs_nonneg _) hδ.le
  have hsum : Integrable (fun ω => ∑ i, ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) P :=
    integrable_finset_sum _ fun i _ => hterm i
  refine ⟨intB (Measurable.ite (measurableSet_lt hWm measurable_const) measurable_const
      measurable_const) 1 (fun ω => by split_ifs <;> norm_num), ?_, ?_, ?_, ?_,
    (integrable_const _).sub hsum, ?_⟩
  · exact intB ((hQm.sub_const 1).pow_const 2) ((Fintype.card ι * δ ^ 2 + 1) ^ 2) fun ω => sq_bdd (by
      have h := hQ ω; have h' := abs_sub (∑ i, ξ i ω ^ 2) 1; rw [abs_one] at h'; linarith)
  · exact intB (hQm.pow_const 2) _ fun ω => sq_bdd (hQ ω)
  · exact intB (hWm.pow_const 2) _ fun ω => sq_bdd (hW ω)
  · exact intB hQm _ hQ
  · rw [integral_sub (integrable_const _) hsum, integral_finsetSum _ fun i _ => hterm i]
    simp [loo_zero ξ hind hmeas hδ hb h0 h1 (steinF z) hfm 3 hf3]

lemma lower_half (z : ℝ) (hδ1 : δ ≤ 1) :
    (P {ω | ∑ i, ξ i ω < z - δ}).toReal ≤ Phi z + 13 / 2 * δ := by
  obtain ⟨hEQ, hW2, hQ2, hQ1⟩ := moments ξ hind hmeas hδ hb h0 h1
  obtain ⟨i0, i1, i2, i3, i4, i5, e5⟩ := pieces ξ hind hmeas hδ hb h0 h1 z (z - δ)
  have hWm : Measurable (fun ω => ∑ i, ξ i ω) := Finset.measurable_sum _ fun i _ => hmeas i
  have hm : ∫ ω, ((if ∑ i, ξ i ω < z - δ then (1:ℝ) else 0) - ((1 / δ) * ((∑ i, ξ i ω ^ 2) - 1) ^ 2 + (δ / 2) * (∑ i, ξ i ω ^ 2) ^ 2 + (δ / 2) * (∑ i, ξ i ω) ^ 2 + (3 * δ) * (∑ i, ξ i ω ^ 2) + δ)) ∂P ≤ ∫ ω, (Phi z - ∑ i, ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) ∂P :=
    integral_mono (i0.sub ((((((i1.const_mul (1 / δ)).add (i2.const_mul (δ / 2))).add
      (i3.const_mul (δ / 2))).add (i4.const_mul (3 * δ))).add (integrable_const δ)))) i5
    (fun ω => pt_lower z δ hδ (fun i => ξ i ω) (fun i => hb i ω))
  rw [int_lin i0 i1 i2 i3 i4, e5, prob_eq_integral hWm, hEQ, hW2] at hm
  have k1 : 1 / δ * ∫ ω, ((∑ i, ξ i ω ^ 2) - 1) ^ 2 ∂P ≤ δ := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hδ]; nlinarith
  have k2 : δ / 2 * ∫ ω, (∑ i, ξ i ω ^ 2) ^ 2 ∂P ≤ δ := by nlinarith
  linarith

lemma upper_half (z : ℝ) (hδ1 : δ ≤ 1) :
    Phi z ≤ (P {ω | ∑ i, ξ i ω < z + δ}).toReal + 13 / 2 * δ := by
  obtain ⟨hEQ, hW2, hQ2, hQ1⟩ := moments ξ hind hmeas hδ hb h0 h1
  obtain ⟨i0, i1, i2, i3, i4, i5, e5⟩ := pieces ξ hind hmeas hδ hb h0 h1 z (z + δ)
  have hWm : Measurable (fun ω => ∑ i, ξ i ω) := Finset.measurable_sum _ fun i _ => hmeas i
  have hm : ∫ ω, (Phi z - ∑ i, ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) ∂P ≤ ∫ ω, ((if ∑ i, ξ i ω < z + δ then (1:ℝ) else 0) + ((1 / δ) * ((∑ i, ξ i ω ^ 2) - 1) ^ 2 + (δ / 2) * (∑ i, ξ i ω ^ 2) ^ 2 + (δ / 2) * (∑ i, ξ i ω) ^ 2 + (3 * δ) * (∑ i, ξ i ω ^ 2) + δ)) ∂P :=
    integral_mono i5 (i0.add ((((((i1.const_mul (1 / δ)).add (i2.const_mul (δ / 2))).add
      (i3.const_mul (δ / 2))).add (i4.const_mul (3 * δ))).add (integrable_const δ))))
    (fun ω => pt_upper z δ hδ (fun i => ξ i ω) (fun i => hb i ω))
  rw [int_lin' i0 i1 i2 i3 i4, e5, prob_eq_integral hWm, hEQ, hW2] at hm
  have k1 : 1 / δ * ∫ ω, ((∑ i, ξ i ω ^ 2) - 1) ^ 2 ∂P ≤ δ := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hδ]; nlinarith
  have k2 : δ / 2 * ∫ ω, (∑ i, ξ i ω ^ 2) ^ 2 ∂P ≤ δ := by nlinarith
  linarith

/-- Berry–Esseen, bounded non-identical summands: `|P(W < z) - Φ(z)| ≤ 7δ`. -/
theorem bdd_BE (hδ1 : δ ≤ 1) (z : ℝ) :
    |(P {ω | ∑ i, ξ i ω < z}).toReal - Phi z| ≤ 7 * δ := by
  have hl := lower_half ξ hind hmeas hδ hb h0 h1 (z + δ) hδ1
  have hu := upper_half ξ hind hmeas hδ hb h0 h1 (z - δ) hδ1
  simp only [add_sub_cancel_right, sub_add_cancel] at hl hu
  have p1 := Phi_sub_le (u := z + δ) (v := z) (by linarith)
  have p2 := Phi_sub_le (u := z) (v := z - δ) (by linarith)
  rw [abs_le]; constructor <;> linarith

end Prob

end P99bcb804

end X34_BdBE

end P99Hyps

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ {Ω : Type} [inst : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
      {ι : Type} [inst_2 : Fintype ι] [DecidableEq ι] (ξ : ι → Ω → ℝ),
      ProbabilityTheory.iIndepFun ξ P →
        (∀ (i : ι), Measurable (ξ i)) →
          ∀ {δ : ℝ},
            (0 : ℝ) < δ →
              (∀ (i : ι) (ω : Ω), |ξ i ω| ≤ δ) →
                (∀ (i : ι), ∫ (ω : Ω), ξ i ω ∂P = (0 : ℝ)) →
                  ∑ i : ι, ∫ (ω : Ω), ξ i ω ^ (2 : ℕ) ∂P = (1 : ℝ) →
                    δ ≤ (1 : ℝ) →
                      ∀ (z : ℝ),
                        |ENNReal.toReal (P {ω : Ω | ∑ i : ι, ξ i ω < z}) -
                              (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) z| ≤
                          (7 : ℝ) * δ := by
  first
  | exact P99bcb804.bdd_BE
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.bdd_BE <;> assumption)
