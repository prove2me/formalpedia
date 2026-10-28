-- Prove2me | solution 1 for EthierKurtz.cramer_iid_bounded_tail_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:43:33.878001+00:00
-- url     : https://prove2.me/submissions/7fbbeb9b-1592-449b-b363-800df578dc3f

import Mathlib
import Theorems.Thm_EthierKurtz_berry_esseen_bounded_independent

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

/-- Mills ratio, lower bound: `x φ(x)/(1+x²) ≤ 1 - Φ(x)` for `x > 0`. -/
lemma mills_lower {x : ℝ} (hx : 0 < x) :
    x * phi x / (1 + x ^ 2) ≤ 1 - cdf (gaussianReal 0 1) x := by
  have hd : ∀ t ∈ Ioi x, HasDerivAt (fun t => -(phi t / t)) ((1 + 1 / t ^ 2) * phi t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hx.trans ht)
    have := ((hasDerivAt_phi t).div (hasDerivAt_id' t) ht0).neg
    refine this.congr_deriv ?_
    field_simp
    ring
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hc : ContinuousWithinAt (fun t => -(phi t / t)) (Ici x) x :=
    ((continuous_phi.continuousAt.div continuousAt_id hx0).neg).continuousWithinAt
  have hpos : ∀ t ∈ Ioi x, 0 ≤ (1 + 1 / t ^ 2) * phi t := fun t _ => by
    have := phi_pos t; positivity
  have hlim : Tendsto (fun t => -(phi t / t)) atTop (𝓝 0) := by
    have := (tendsto_phi_atTop.mul tendsto_inv_atTop_zero).neg
    simpa [div_eq_mul_inv] using this
  have hint := integrableOn_Ioi_deriv_of_nonneg hc hd hpos hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonneg hc hd hpos hlim
  -- φ(x)/x = ∫ (1+1/t²) φ ≤ (1+1/x²) ∫ φ
  have hle : ∫ t in Ioi x, (1 + 1 / t ^ 2) * phi t ≤ ∫ t in Ioi x, (1 + 1 / x ^ 2) * phi t := by
    refine setIntegral_mono_on hint (integrable_phi.integrableOn.const_mul _) measurableSet_Ioi
      (fun t ht => ?_)
    have hxt : x < t := ht
    have h1 : 1 / t ^ 2 ≤ 1 / x ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    nlinarith [phi_pos t]
  rw [heq, integral_const_mul, ← one_sub_cdf_std] at hle
  have hval : (0 : ℝ) - -(phi x / x) = phi x / x := by ring
  rw [hval] at hle
  rw [div_le_iff₀ (by positivity)]
  have hk : x * phi x = x ^ 2 * (phi x / x) := by field_simp
  rw [hk]
  have hk2 : (1 + x ^ 2) = x ^ 2 * (1 + 1 / x ^ 2) := by field_simp; ring
  rw [hk2]
  have hx2 : 0 < x ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hle hx2.le]

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

lemma cdf_std_pos (x : ℝ) : 0 < cdf (gaussianReal 0 1) x := by
  rw [cdf_std_eq]
  have hsupp : Function.support phi = univ := by
    ext t; simp [(phi_pos t).ne']
  have hpos : 0 < volume (Function.support phi ∩ Iic x) := by
    rw [hsupp, univ_inter, Real.volume_Iic]; exact ENNReal.zero_lt_top
  exact (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => (phi_pos t).le)
    integrable_phi.integrableOn).mpr hpos

lemma cdf_std_lt_one (x : ℝ) : cdf (gaussianReal 0 1) x < 1 := by
  have := cdf_std_pos (-x)
  rw [cdf_std_neg] at this
  linarith

/-! ### Stein solution for the indicator `1{w ≤ z}` (Chen–Goldstein–Shao, Lemma 2.3) -/

/-- Standard normal cdf as a real function. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-! ## Child C (Tusnády quantile inequality), generic over the family of sum laws. -/

lemma hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (phi x) x := hasDerivAt_cdf_std x

lemma one_sub_Phi_pos (w : ℝ) : 0 < 1 - Phi w := by
  have := cdf_std_lt_one w; unfold Phi; linarith

/-! ## Gaussian hazard `Hz = φ/(1-Φ)` and the two-sided log-tail Taylor bound (KMT 1976 II, (4.5)). -/

/-- Gaussian hazard rate `Hz w = φ(w)/(1-Φ(w))`. -/
noncomputable def Hz (w : ℝ) : ℝ := phi w / (1 - Phi w)

lemma Hz_pos (w : ℝ) : 0 < Hz w := div_pos (phi_pos w) (one_sub_Phi_pos w)

lemma hasDerivAt_Hz (w : ℝ) : HasDerivAt Hz (Hz w * (Hz w - w)) w := by
  have hG := one_sub_Phi_pos w
  have h := (hasDerivAt_phi w).div ((hasDerivAt_Phi w).const_sub 1) hG.ne'
  exact h.congr_deriv (by unfold Hz; field_simp <;> ring)

lemma le_Hz (w : ℝ) : w ≤ Hz w := by
  rcases le_or_gt w 0 with hw | hw
  · exact hw.trans (Hz_pos w).le
  · have h := mills_upper hw
    have hG := one_sub_Phi_pos w
    unfold Hz; rw [le_div_iff₀ hG]
    have h2 : (1 - Phi w) * w ≤ phi w := by
      unfold Phi; rw [← le_div_iff₀ hw]; exact h
    linarith

lemma Hz_mono : Monotone Hz :=
  monotone_of_hasDerivAt_nonneg hasDerivAt_Hz fun w =>
    mul_nonneg (Hz_pos w).le (sub_nonneg.2 (le_Hz w))

lemma phi_le_phi_zero (w : ℝ) : phi w ≤ phi 0 := by
  unfold phi
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  nlinarith [sq_nonneg w]

lemma phi_one : phi 1 = phi 0 * Real.exp (-(1 / 2)) := by
  unfold phi; norm_num

lemma Hz_deriv_le {w : ℝ} (hw : 0 ≤ w) : Hz w * (Hz w - w) ≤ 16 := by
  set G := 1 - Phi w with hGdef
  set p := phi w with hpdef
  have hG : 0 < G := one_sub_Phi_pos w
  have hp : 0 < p := phi_pos w
  have e : Hz w * (Hz w - w) = p * (p - w * G) / G ^ 2 := by
    unfold Hz; rw [← hGdef, ← hpdef]; field_simp
  rw [e, div_le_iff₀ (by positivity)]
  rcases le_or_gt 1 w with h1 | h1
  · have hml := mills_lower (by linarith : (0 : ℝ) < w)
    set A := 1 + w ^ 2 with hA
    have hA0 : 0 < A := by positivity
    have hm : w * p ≤ A * G := by
      have : w * p / A ≤ G := by simpa [hGdef, Phi] using hml
      rwa [div_le_iff₀ hA0, mul_comm G] at this
    -- A (p - wG) ≤ p
    have s1 : A * (p - w * G) ≤ p := by
      have := mul_le_mul_of_nonneg_left hm hw
      nlinarith
    have s2 : A * (p * (p - w * G)) ≤ p ^ 2 := by nlinarith
    have s3 : (w * p) ^ 2 ≤ (A * G) ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
    have s4 : w ^ 2 * (A * (p * (p - w * G))) ≤ A ^ 2 * G ^ 2 := by
      have := mul_le_mul_of_nonneg_left s2 (sq_nonneg w)
      nlinarith
    have s5 : w ^ 2 * (p * (p - w * G)) ≤ A * G ^ 2 := by
      have h' : A * (w ^ 2 * (p * (p - w * G))) ≤ A * (A * G ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left h' hA0
    have hw2 : 1 ≤ w ^ 2 := by nlinarith
    have s6 : A * G ^ 2 ≤ 2 * w ^ 2 * G ^ 2 := by
      have : A ≤ 2 * w ^ 2 := by rw [hA]; linarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg G)
    have s7 : p * (p - w * G) ≤ 2 * G ^ 2 := by
      have h' : w ^ 2 * (p * (p - w * G)) ≤ w ^ 2 * (2 * G ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left h' (by linarith)
    nlinarith [sq_nonneg G]
  · -- 0 ≤ w < 1
    have hG1 : 1 - Phi 1 ≤ G := by
      have : Phi w ≤ Phi 1 := (cdf (gaussianReal 0 1)).mono h1.le
      linarith
    have hml := mills_lower (by norm_num : (0 : ℝ) < 1)
    have hG1' : phi 1 / 2 ≤ 1 - Phi 1 := by
      have : (1 : ℝ) * phi 1 / (1 + 1 ^ 2) = phi 1 / 2 := by norm_num
      rw [← this]; simpa [Phi] using hml
    have hp0 : p ≤ phi 0 := phi_le_phi_zero w
    have he : Real.exp (-(1 / 2)) ^ 2 = Real.exp (-1) := by
      rw [← Real.exp_nat_mul]; norm_num
    have he1 : (1 : ℝ) / 4 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have hph0 : 0 < phi 0 := phi_pos 0
    have hGlow : phi 0 * Real.exp (-(1 / 2)) / 2 ≤ G := by
      rw [← phi_one]; linarith
    have hGsq : (phi 0 * Real.exp (-(1 / 2)) / 2) ^ 2 ≤ G ^ 2 :=
      pow_le_pow_left₀ (by positivity) hGlow 2
    have hsq : (phi 0 * Real.exp (-(1 / 2)) / 2) ^ 2 = phi 0 ^ 2 * Real.exp (-1) / 4 := by
      rw [div_pow, mul_pow, he]; ring
    have hwG : 0 ≤ w * G := by positivity
    have : p * (p - w * G) ≤ phi 0 ^ 2 := by nlinarith
    nlinarith [sq_nonneg (phi 0)]

lemma Hz_lip {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : Hz b - Hz a ≤ 16 * (b - a) := by
  have hanti : AntitoneOn (fun w => Hz w - 16 * w) (Set.Ici 0) := by
    have hd : ∀ w, HasDerivAt (fun w => Hz w - 16 * w) (Hz w * (Hz w - w) - 16) w := fun w => by
      have := (hasDerivAt_Hz w).sub ((hasDerivAt_id' w).const_mul 16)
      rwa [mul_one] at this
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun w _ => (hd w).continuousAt.continuousWithinAt)
      (fun w _ => (hd w).differentiableAt.differentiableWithinAt) fun w hw => ?_
    rw [interior_Ici] at hw
    rw [(hd w).deriv]; linarith [Hz_deriv_le (le_of_lt (Set.mem_Ioi.1 hw))]
  have := hanti (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hab)) hab
  simp only at this; linarith

lemma hasDerivAt_tailexp {q : ℝ → ℝ} {q' w : ℝ} (hq : HasDerivAt q q' w) :
    HasDerivAt (fun w => (1 - Phi w) * Real.exp (q w))
      (Real.exp (q w) * (1 - Phi w) * (q' - Hz w)) w := by
  have hG := one_sub_Phi_pos w
  have h := ((hasDerivAt_Phi w).const_sub 1).mul hq.exp
  exact h.congr_deriv (by unfold Hz; field_simp <;> ring)

/-- Convexity side of (4.5): `1 - Φ(b) ≤ (1 - Φ(a)) e^{-Hz(a)(b-a)}` for all `a, b`. -/
lemma tail_ratio_upper (a b : ℝ) :
    1 - Phi b ≤ (1 - Phi a) * Real.exp (-(Hz a * (b - a))) := by
  set g : ℝ → ℝ := fun w => (1 - Phi w) * Real.exp (Hz a * (w - a)) with hg
  have hd : ∀ w, HasDerivAt g (Real.exp (Hz a * (w - a)) * (1 - Phi w) * (Hz a - Hz w)) w :=
    fun w => hasDerivAt_tailexp (by simpa using ((hasDerivAt_id w).sub_const a).const_mul (Hz a))
  have hpos : ∀ w, 0 < Real.exp (Hz a * (w - a)) * (1 - Phi w) := fun w =>
    mul_pos (Real.exp_pos _) (one_sub_Phi_pos w)
  have key : g b ≤ g a := by
    rcases le_total a b with hab | hab
    · have hanti : AntitoneOn g (Set.Ici a) := antitoneOn_of_deriv_nonpos (convex_Ici a)
        (fun w _ => (hd w).continuousAt.continuousWithinAt)
        (fun w _ => (hd w).differentiableAt.differentiableWithinAt) fun w hw => by
          rw [interior_Ici] at hw; rw [(hd w).deriv]
          exact mul_nonpos_of_nonneg_of_nonpos (hpos w).le
            (sub_nonpos.2 (Hz_mono (le_of_lt (Set.mem_Ioi.1 hw))))
      exact hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hab) hab
    · have hmono : MonotoneOn g (Set.Iic a) := monotoneOn_of_deriv_nonneg (convex_Iic a)
        (fun w _ => (hd w).continuousAt.continuousWithinAt)
        (fun w _ => (hd w).differentiableAt.differentiableWithinAt) fun w hw => by
          rw [interior_Iic] at hw; rw [(hd w).deriv]
          exact mul_nonneg (hpos w).le (sub_nonneg.2 (Hz_mono (le_of_lt (Set.mem_Iio.1 hw))))
      exact hmono (Set.mem_Iic.2 hab) (Set.mem_Iic.2 le_rfl) hab
  simp only [hg, sub_self, mul_zero, Real.exp_zero, mul_one] at key
  have e : 1 - Phi b = (1 - Phi b) * Real.exp (Hz a * (b - a)) * Real.exp (-(Hz a * (b - a))) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [e]
  exact mul_le_mul_of_nonneg_right key (Real.exp_pos _).le

/-- Second-order side of (4.5): for `a, b ≥ 0`,
`(1 - Φ(a)) e^{-Hz(a)(b-a) - 8(b-a)²} ≤ 1 - Φ(b)`. -/
lemma tail_ratio_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 - Phi a) * Real.exp (-(Hz a * (b - a)) - 8 * (b - a) ^ 2) ≤ 1 - Phi b := by
  set f : ℝ → ℝ := fun w => (1 - Phi w) * Real.exp (Hz a * (w - a) + 8 * (w - a) ^ 2) with hf
  have hd : ∀ w, HasDerivAt f (Real.exp (Hz a * (w - a) + 8 * (w - a) ^ 2) * (1 - Phi w) *
      ((Hz a + 16 * (w - a)) - Hz w)) w := by
    intro w
    have h1 := ((hasDerivAt_id' w).sub_const a).const_mul (Hz a)
    have h2 := (((hasDerivAt_id' w).sub_const a).pow 2).const_mul 8
    have hq : HasDerivAt (fun w => Hz a * (w - a) + 8 * (w - a) ^ 2) (Hz a + 16 * (w - a)) w :=
      (h1.add h2).congr_deriv (by norm_num <;> ring)
    exact hasDerivAt_tailexp hq
  have hpos : ∀ w, 0 < Real.exp (Hz a * (w - a) + 8 * (w - a) ^ 2) * (1 - Phi w) := fun w =>
    mul_pos (Real.exp_pos _) (one_sub_Phi_pos w)
  have key : f a ≤ f b := by
    rcases le_total a b with hab | hab
    · have hmono : MonotoneOn f (Set.Ici a) := monotoneOn_of_deriv_nonneg (convex_Ici a)
        (fun w _ => (hd w).continuousAt.continuousWithinAt)
        (fun w _ => (hd w).differentiableAt.differentiableWithinAt) fun w hw => by
          rw [interior_Ici] at hw; rw [(hd w).deriv]
          have := Hz_lip ha (le_of_lt (Set.mem_Ioi.1 hw))
          exact mul_nonneg (hpos w).le (by linarith)
      exact hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hab) hab
    · have hanti : AntitoneOn f (Set.Icc 0 a) := antitoneOn_of_deriv_nonpos (convex_Icc 0 a)
        (fun w _ => (hd w).continuousAt.continuousWithinAt)
        (fun w _ => (hd w).differentiableAt.differentiableWithinAt) fun w hw => by
          rw [interior_Icc] at hw; rw [(hd w).deriv]
          have := Hz_lip (le_of_lt hw.1) (le_of_lt hw.2)
          exact mul_nonpos_of_nonneg_of_nonpos (hpos w).le (by linarith)
      exact hanti (Set.mem_Icc.2 ⟨hb, hab⟩) (Set.mem_Icc.2 ⟨ha, le_rfl⟩) hab
  simp only [hf, sub_self, mul_zero, Real.exp_zero, mul_one, zero_add, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at key
  have e : (1 - Phi a) * Real.exp (-(Hz a * (b - a)) - 8 * (b - a) ^ 2) =
      (1 - Phi a) * (Real.exp (Hz a * (b - a) + 8 * (b - a) ^ 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [e, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact key

lemma Phi_zero : Phi 0 = 1 / 2 := by
  have h := cdf_std_neg 0
  simp only [neg_zero] at h
  unfold Phi; linarith

lemma Hz_zero_le : Hz 0 ≤ 1 := by
  unfold Hz; rw [Phi_zero, div_le_one (by norm_num)]
  unfold phi
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
    Real.exp_zero, mul_one]
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h2 : (2 : ℝ) ≤ √(2 * π) := by
    calc (2 : ℝ) = √4 := h4.symm
      _ ≤ √(2 * π) := Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith

lemma Hz_le_lin {a : ℝ} (ha : 0 ≤ a) : Hz a ≤ 1 + 16 * a := by
  have := Hz_lip le_rfl ha; linarith [Hz_zero_le]

end P99bcb804

end X19_Mills

section X28_DtE

/-! R4 / DtE: lower tail of the density -> Tusnady lemma:
`(1 - Φ s) e^{-cL ε s³} ≤ ∫_{Ioi s} h` for `1 ≤ s ≤ (ε0/2)/ε`. -/

open MeasureTheory Real Set Filter

namespace P99bcb804

lemma exp_neg_two_le {y : ℝ} (hy : 0 ≤ y) (hy2 : y ≤ 1 / 2) : exp (-(2 * y)) ≤ 1 - y := by
  have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * y)
  have he : exp (-(2 * y)) * exp (2 * y) = 1 := by rw [← exp_add]; simp
  have hpos := exp_pos (-(2 * y))
  have h1 : 1 ≤ (1 + 2 * y + (2 * y) ^ 2 / 2) * (1 - y) := by nlinarith
  have h2 : (1 + 2 * y + (2 * y) ^ 2 / 2) * (1 - y) ≤ exp (2 * y) * (1 - y) :=
    mul_le_mul_of_nonneg_right hq (by linarith)
  nlinarith

end P99bcb804

end X28_DtE

section X32_Lap

/-! Laplace-transform step of the Esscher-tilt argument (KMT 1976 II, Lemma B):
`E[e^{-uW}; W > 0]` moves by at most `2η` when the law of `W` moves by `η` in Kolmogorov
distance, and for a standard Gaussian it equals `e^{u²/2}(1 - Φ(u))`. -/

open MeasureTheory ProbabilityTheory Real Set

namespace P99bcb804

/-- `g_u(w) = e^{-uw} 1{w > 0}`. -/
noncomputable def lapG (u w : ℝ) : ℝ := if 0 < w then exp (-(u * w)) else 0

lemma lapG_nonneg (u w : ℝ) : 0 ≤ lapG u w := by
  unfold lapG; split_ifs <;> positivity

lemma lapG_le_one {u : ℝ} (hu : 0 ≤ u) (w : ℝ) : lapG u w ≤ 1 := by
  unfold lapG; split_ifs with h
  · exact exp_le_one_iff.mpr (by nlinarith)
  · norm_num

lemma measurable_lapG (u : ℝ) : Measurable (lapG u) := by
  unfold lapG
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

lemma level_empty {u t : ℝ} (hu : 0 ≤ u) (ht : 1 ≤ t) : {w | t < lapG u w} = ∅ := by
  ext w; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
  exact (lapG_le_one hu w).trans ht

lemma level_cmp (ν1 ν2 : Measure ℝ) [IsProbabilityMeasure ν1] [IsProbabilityMeasure ν2] {η : ℝ}
    (hlt : ∀ c, |ν1.real (Iio c) - ν2.real (Iio c)| ≤ η)
    (hle : |ν1.real (Iic 0) - ν2.real (Iic 0)| ≤ η) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    |ν1.real {w | t < lapG u w} - ν2.real {w | t < lapG u w}| ≤ 2 * η := by
  have hη : 0 ≤ η := (abs_nonneg _).trans hle
  rcases le_or_gt 1 t with h1 | h1
  · rw [level_empty hu h1]; simp; linarith
  rcases eq_or_lt_of_le hu with hu0 | hu0
  · subst hu0
    have e : {w | t < lapG 0 w} = (Iic 0)ᶜ := by
      ext w; simp only [mem_setOf_eq, mem_compl_iff, mem_Iic, not_le, lapG, zero_mul, neg_zero,
        exp_zero]
      split_ifs with h <;> constructor <;> intro h' <;> first | linarith | exact h
    rw [e, measureReal_compl measurableSet_Iic, measureReal_compl measurableSet_Iic,
      probReal_univ, probReal_univ]
    rw [show (1 - ν1.real (Iic 0)) - (1 - ν2.real (Iic 0)) = -(ν1.real (Iic 0) - ν2.real (Iic 0))
      by ring, abs_neg]
    linarith
  · have hlog : log t < 0 := log_neg ht h1
    set c := -log t / u with hc
    have hc0 : 0 < c := div_pos (by linarith) hu0
    have e : {w | t < lapG u w} = Iio c \ Iic 0 := by
      ext w
      simp only [mem_setOf_eq, mem_diff, mem_Iio, mem_Iic, not_le, lapG]
      split_ifs with h
      · rw [← log_lt_iff_lt_exp ht, hc, lt_div_iff₀ hu0]
        constructor
        · intro h'; exact ⟨by linarith, h⟩
        · intro h'; linarith [h'.1]
      · constructor
        · intro h'; linarith
        · intro h'; exact absurd h'.2 h
    rw [e, measureReal_diff (Iic_subset_Iio.mpr hc0) measurableSet_Iic,
      measureReal_diff (Iic_subset_Iio.mpr hc0) measurableSet_Iic]
    have := hlt c
    rw [show ν1.real (Iio c) - ν1.real (Iic 0) - (ν2.real (Iio c) - ν2.real (Iic 0))
      = (ν1.real (Iio c) - ν2.real (Iio c)) - (ν1.real (Iic 0) - ν2.real (Iic 0)) by ring]
    exact (abs_sub _ _).trans (by linarith)

lemma level_anti (ν : Measure ℝ) [IsProbabilityMeasure ν] (u : ℝ) :
    Antitone (fun t => ν.real {w | t < lapG u w}) :=
  fun a b hab => measureReal_mono (fun w hw => lt_of_le_of_lt hab hw)

lemma lap_layer (ν : Measure ℝ) [IsProbabilityMeasure ν] {u : ℝ} (hu : 0 ≤ u) :
    ∫ w, lapG u w ∂ν = ∫ t in Ioc 0 1, ν.real {w | t < lapG u w} := by
  have hint : Integrable (lapG u) ν :=
    Integrable.of_bound (measurable_lapG u).aestronglyMeasurable 1
      (ae_of_all _ fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (lapG_nonneg u w)]; exact lapG_le_one hu w)
  rw [hint.integral_eq_integral_meas_lt (ae_of_all _ (lapG_nonneg u))]
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun t ht => ?_
  have : 1 ≤ t := by
    rcases ht with ⟨h1, h2⟩
    simp only [mem_Ioc, not_and, not_le] at h2
    exact (h2 h1).le
  rw [level_empty hu this]; simp

lemma level_intOn (ν : Measure ℝ) [IsProbabilityMeasure ν] (u : ℝ) :
    IntegrableOn (fun t => ν.real {w | t < lapG u w}) (Ioc 0 1) :=
  Measure.integrableOn_of_bounded (M := 1) (by simp [Real.volume_Ioc])
    (level_anti ν u).measurable.aestronglyMeasurable
    (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)

/-- Laplace comparison: Kolmogorov distance `η` moves `E[e^{-uW}; W > 0]` by at most `2η`. -/
theorem lap_cmp (ν1 ν2 : Measure ℝ) [IsProbabilityMeasure ν1] [IsProbabilityMeasure ν2] {η : ℝ}
    (hlt : ∀ c, |ν1.real (Iio c) - ν2.real (Iio c)| ≤ η)
    (hle : |ν1.real (Iic 0) - ν2.real (Iic 0)| ≤ η) {u : ℝ} (hu : 0 ≤ u) :
    |∫ w, lapG u w ∂ν1 - ∫ w, lapG u w ∂ν2| ≤ 2 * η := by
  rw [lap_layer ν1 hu, lap_layer ν2 hu, ← integral_sub (level_intOn ν1 u) (level_intOn ν2 u)]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0:ℝ) 1) (C := 2 * η)
    (f := fun t => ν1.real {w | t < lapG u w} - ν2.real {w | t < lapG u w})
    (by simp [Real.volume_Ioc]) (fun t ht => by
      rw [Real.norm_eq_abs]; exact level_cmp ν1 ν2 hlt hle hu ht.1)
  rw [Real.norm_eq_abs] at this
  simpa [Real.volume_Ioc] using this

/-- Gaussian Laplace identity `E[e^{-uZ}; Z > 0] = e^{u²/2}(1 - Φ(u))`. -/
theorem lap_gauss (u : ℝ) :
    ∫ w, lapG u w ∂(gaussianReal 0 1) = exp (u ^ 2 / 2) * (1 - Phi u) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [gaussianPDFReal_std, smul_eq_mul]
  have e1 : (fun x => phi x * lapG u x)
      = fun x => exp (u ^ 2 / 2) * Set.indicator (Ioi u) phi (x + u) := by
    funext x
    unfold lapG
    simp only [Set.indicator_apply, mem_Ioi]
    split_ifs with h1 h2 h2
    · have hx : exp (-(x ^ 2 / 2)) * exp (-(u * x))
          = exp (u ^ 2 / 2) * exp (-((x + u) ^ 2 / 2)) := by
        rw [← exp_add, ← exp_add]; congr 1; ring
      unfold phi
      linear_combination (√(2 * π))⁻¹ * hx
    · exfalso; linarith
    · exfalso; linarith
    · simp
  rw [e1, integral_const_mul,
    integral_add_right_eq_self (fun x => Set.indicator (Ioi u) phi x) u,
    integral_indicator measurableSet_Ioi, ← one_sub_cdf_std]
  rfl

end P99bcb804

end X32_Lap

section X34_BdBE

/-! Berry–Esseen for independent, non-identically distributed, uniformly bounded summands
(Stein's method, bounded case, cf. Chen–Goldstein–Shao, Normal Approximation by Stein's Method,
§3.1): if `|ξ_i| ≤ δ ≤ 1`, `E ξ_i = 0`, `Σ E ξ_i² = 1`, then `|P(W < z) - Φ(z)| ≤ 7δ`. -/

open MeasureTheory ProbabilityTheory Real Set Finset

namespace P99bcb804

section Prob

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type} [Fintype ι] [DecidableEq ι]

variable (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P) (hmeas : ∀ i, Measurable (ξ i)) {δ : ℝ}
  (hδ : 0 < δ) (hb : ∀ i ω, |ξ i ω| ≤ δ) (h0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
  (h1 : ∑ i, ∫ ω, ξ i ω ^ 2 ∂P = 1)
include hind hmeas hδ hb h0 h1

/-- Berry–Esseen, bounded non-identical summands: `|P(W < z) - Φ(z)| ≤ 7δ`. -/
theorem bdd_BE (hδ1 : δ ≤ 1) (z : ℝ) :
    |(P {ω | ∑ i, ξ i ω < z}).toReal - Phi z| ≤ 7 * δ := by
  have hfact := @EthierKurtz.berry_esseen_bounded_independent
  apply hfact <;> assumption

end Prob

end P99bcb804

end X34_BdBE

section X35_Tilt

/-! Esscher tilt of Rademacher-weighted sums (KMT 1976 II, Lemma B, pp.42-43):
tilted Bernoulli product measure `Ph a`, the change-of-measure identity for
`#{e : t < Σ s_i d_i} / 2^N`, and the Berry–Esseen + Laplace comparison under the tilt. -/

open MeasureTheory ProbabilityTheory Real Set Finset

namespace P99bcb804

section BE

variable {N : ℕ}

lemma gauss_Iio (c : ℝ) : (gaussianReal 0 1).real (Iio c) = Phi c := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [Phi, cdf_eq_real, measureReal_def, measureReal_def, measure_congr Iio_ae_eq_Iic]

end BE

end P99bcb804

end X35_Tilt

section X38_Cram2

/-! KMT 1976 II, Lemma B: the elementary estimates of the tilt parameter, cumulant and
variance, and the final two-sided combination. -/

open Real Finset

namespace P99bcb804

variable {N : ℕ}

lemma psi_eq (u : ℝ) : exp (u ^ 2 / 2) * (1 - Phi u) = 1 / (√(2 * π) * Hz u) := by
  have hG := one_sub_Phi_pos u
  have hs : 0 < √(2 * π) := by positivity
  have hz := Hz_pos u
  rw [eq_div_iff (mul_pos hs hz).ne']
  unfold Hz phi
  field_simp
  rw [← exp_add]
  simp

lemma ratio_bounds {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    exp (x ^ 2 / 2) * (1 - Phi x) *
        exp ((u ^ 2 - x ^ 2) / 2 - Hz x * (u - x) - 8 * (u - x) ^ 2) ≤
      exp (u ^ 2 / 2) * (1 - Phi u) ∧
    exp (u ^ 2 / 2) * (1 - Phi u) ≤
      exp (x ^ 2 / 2) * (1 - Phi x) * exp ((u ^ 2 - x ^ 2) / 2 - Hz x * (u - x)) := by
  have hU := tail_ratio_upper x u
  have hL := tail_ratio_lower hx hu
  have e1 : exp (x ^ 2 / 2) * (1 - Phi x) *
      exp ((u ^ 2 - x ^ 2) / 2 - Hz x * (u - x) - 8 * (u - x) ^ 2) =
      exp (u ^ 2 / 2) * ((1 - Phi x) * exp (-(Hz x * (u - x)) - 8 * (u - x) ^ 2)) := by
    rw [mul_comm (exp (x ^ 2 / 2)), mul_assoc, ← exp_add, mul_left_comm, ← exp_add]; ring_nf
  have e2 : exp (x ^ 2 / 2) * (1 - Phi x) * exp ((u ^ 2 - x ^ 2) / 2 - Hz x * (u - x)) =
      exp (u ^ 2 / 2) * ((1 - Phi x) * exp (-(Hz x * (u - x)))) := by
    rw [mul_comm (exp (x ^ 2 / 2)), mul_assoc, ← exp_add, mul_left_comm, ← exp_add]; ring_nf
  rw [e1, e2]
  exact ⟨mul_le_mul_of_nonneg_left hL (exp_pos _).le, mul_le_mul_of_nonneg_left hU (exp_pos _).le⟩

/-- Final combination: an additive error `r` relative to `ψ` plus two-sided log bounds. -/
lemma combine {P L0 ψu G x lo hi r T : ℝ} (hψ : 0 < ψu) (hG : 0 < G)
    (hP : |P - exp L0 * ψu| ≤ exp L0 * (r * ψu)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (hlo : G * exp (x ^ 2 / 2) * exp lo ≤ ψu) (hhi : ψu ≤ G * exp (x ^ 2 / 2) * exp hi)
    (hT1 : -T ≤ L0 + x ^ 2 / 2 + lo - 2 * r) (hT2 : L0 + x ^ 2 / 2 + hi + r ≤ T) :
    G * exp (-T) ≤ P ∧ P ≤ G * exp T := by
  rw [abs_le] at hP
  have hE := exp_pos L0
  constructor
  · have h1 : exp L0 * ψu * exp (-(2 * r)) ≤ exp L0 * ψu * (1 - r) :=
      mul_le_mul_of_nonneg_left (exp_neg_two_le hr0 hr1) (by positivity)
    have h2 : G * exp (x ^ 2 / 2) * exp lo * (exp L0 * exp (-(2 * r))) ≤
        ψu * (exp L0 * exp (-(2 * r))) := mul_le_mul_of_nonneg_right hlo (by positivity)
    have e : G * exp (x ^ 2 / 2) * exp lo * (exp L0 * exp (-(2 * r))) =
        G * exp (L0 + x ^ 2 / 2 + lo - 2 * r) := by
      rw [show L0 + x ^ 2 / 2 + lo - 2 * r = x ^ 2 / 2 + lo + (L0 + -(2 * r)) by ring,
        exp_add, exp_add, exp_add]; ring
    have h3 : G * exp (-T) ≤ G * exp (L0 + x ^ 2 / 2 + lo - 2 * r) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.2 hT1) hG.le
    nlinarith
  · have h1 : exp L0 * ψu * (1 + r) ≤ exp L0 * ψu * exp r :=
      mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp r]) (by positivity)
    have h2 : ψu * (exp L0 * exp r) ≤ G * exp (x ^ 2 / 2) * exp hi * (exp L0 * exp r) :=
      mul_le_mul_of_nonneg_right hhi (by positivity)
    have e : G * exp (x ^ 2 / 2) * exp hi * (exp L0 * exp r) =
        G * exp (L0 + x ^ 2 / 2 + hi + r) := by
      rw [show L0 + x ^ 2 / 2 + hi + r = x ^ 2 / 2 + hi + (L0 + r) by ring,
        exp_add, exp_add, exp_add]; ring
    have h3 : G * exp (L0 + x ^ 2 / 2 + hi + r) ≤ G * exp T :=
      mul_le_mul_of_nonneg_left (exp_le_exp.2 hT2) hG.le
    nlinarith

end P99bcb804

end X38_Cram2

section X55_Rot

/-! P2 ingredient: the 2-D rotation `(a, b) ↦ ((a+b)/√2, (a-b)/√2)` preserves the standard
Gaussian on `ℝ × ℝ`; hence the Gaussian split `T ↦ (T ± √(2^(n+1)) z)/2` of the tree `G`
turns `N(0, 2^(n+1)) ⊗ N(0,1)` into `N(0, 2^n) ⊗ N(0, 2^n)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- `ℝ × ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def e2 : ℝ × ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

end P99bcb804

end X55_Rot

section X60_IidA

/-! E (iid Cramér, KMT 1975 Part I (2.6) / Petrov): cumulant facts for a bounded, centred law
with unit second moment: `Λ = cgf id F`, `μ_t = Λ'(t)`, `V t = Λ''(t)`;
`V t ∈ [e^{-2|t|K}, e^{|t|K}]`, `|Λ t - t²/2| ≤ 2K t³`, `|μ_t - t| ≤ 4K t²`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace P99bcb804

section IidA

variable {F : Measure ℝ} [IsProbabilityMeasure F] {K : ℝ}

lemma int_of_ae_bdd {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ) (h : ∀ᵐ x ∂F, |g x| ≤ C) :
    Integrable g F :=
  Integrable.of_bound hg.aestronglyMeasurable C (h.mono fun x hx => by rwa [Real.norm_eq_abs])

lemma tx_le (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (t : ℝ) : ∀ᵐ x ∂F, |t * x| ≤ |t| * K :=
  hsupp.mono fun x hx => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)

lemma iexp (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (t : ℝ) : Integrable (fun x : ℝ => exp (t * x)) F :=
  int_of_ae_bdd (by fun_prop) (exp (|t| * K)) ((tx_le hsupp t).mono fun x hx => by
    rw [abs_exp]; exact exp_le_exp.2 ((le_abs_self _).trans hx))

lemma ipow_exp (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (k : ℕ) (t c : ℝ) :
    Integrable (fun x : ℝ => (x - c) ^ k * exp (t * x)) F :=
  int_of_ae_bdd (by fun_prop) ((K + |c|) ^ k * exp (|t| * K))
    ((hsupp.and (tx_le hsupp t)).mono fun x hx => by
      rw [abs_mul, abs_pow, abs_exp]
      have h1 : |x - c| ≤ K + |c| := (abs_sub _ _).trans (by linarith [hx.1])
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 k)
        (exp_le_exp.2 ((le_abs_self _).trans hx.2)) (exp_pos _).le
        (pow_nonneg ((abs_nonneg _).trans h1) k))

lemma iid_int (hsupp : ∀ᵐ x ∂F, |x| ≤ K) : Integrable (fun x : ℝ => x) F :=
  int_of_ae_bdd measurable_id K hsupp

lemma hI (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (t : ℝ) :
    t ∈ interior (integrableExpSet (fun x : ℝ => x) F) := by
  have : integrableExpSet (fun x : ℝ => x) F = univ :=
    eq_univ_of_forall fun t => iexp hsupp t
  rw [this, interior_univ]; trivial

lemma one_le_mgf (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (t : ℝ) :
    1 ≤ mgf (fun x : ℝ => x) F t := by
  have ia : Integrable (fun x : ℝ => 1 + t * x) F :=
    (integrable_const 1).add ((iid_int hsupp).const_mul t)
  have e : ∫ x, (1 + t * x) ∂F = 1 := by
    rw [integral_add (integrable_const _) ((iid_int hsupp).const_mul t), integral_const_mul, hm]
    simp
  have h := integral_mono ia (iexp hsupp t)
    (fun x => by simpa [add_comm] using add_one_le_exp (t * x))
  rw [e] at h
  simpa [mgf] using h

lemma mgf_le (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (t : ℝ) :
    mgf (fun x : ℝ => x) F t ≤ exp (|t| * K) := by
  have h := integral_mono_ae (iexp hsupp t) (integrable_const (exp (|t| * K)))
    ((tx_le hsupp t).mono fun x hx => exp_le_exp.2 ((le_abs_self _).trans hx))
  simpa [mgf] using h

/-- second derivative of the cumulant generating function. -/
noncomputable def Vt (F : Measure ℝ) (t : ℝ) : ℝ := iteratedDeriv 2 (cgf (fun x : ℝ => x) F) t

/-- tilted mean `Λ'(t)`. -/
noncomputable def tmean (F : Measure ℝ) (t : ℝ) : ℝ := deriv (cgf (fun x : ℝ => x) F) t

lemma ipow (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (k : ℕ) : Integrable (fun x : ℝ => x ^ k) F := by
  simpa using ipow_exp hsupp k 0 0

lemma Vt_upper (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1)
    (t : ℝ) : Vt F t ≤ exp (|t| * K) := by
  unfold Vt
  rw [iteratedDeriv_two_cgf (hI hsupp t)]
  have hM := one_le_mgf hsupp hm t
  have i1 : Integrable (fun x : ℝ => x ^ 2 * exp (t * x)) F := by
    simpa using ipow_exp hsupp 2 t 0
  have h1 : ∫ x, x ^ 2 * exp (t * x) ∂F ≤ exp (|t| * K) := by
    have := integral_mono_ae i1 ((ipow hsupp 2).mul_const (exp (|t| * K)))
      ((tx_le hsupp t).mono fun x hx => mul_le_mul_of_nonneg_left
        (exp_le_exp.2 ((le_abs_self _).trans hx)) (sq_nonneg x))
    rwa [integral_mul_const, hv, one_mul] at this
  have h0 : 0 ≤ ∫ x, x ^ 2 * exp (t * x) ∂F :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg x) (exp_pos _).le
  have h2 : (∫ x, x ^ 2 * exp (t * x) ∂F) / mgf (fun x : ℝ => x) F t ≤
      ∫ x, x ^ 2 * exp (t * x) ∂F := div_le_self h0 hM
  have h3 := sq_nonneg (deriv (cgf (fun x : ℝ => x) F) t)
  linarith

lemma sq_int (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1) (c : ℝ) :
    ∫ x, (x - c) ^ 2 ∂F = 1 + c ^ 2 := by
  have e : (fun x : ℝ => (x - c) ^ 2) = fun x => x ^ 2 + ((-2 * c) * x + c ^ 2) := by
    funext x; ring
  rw [e, integral_add (ipow hsupp 2) (show Integrable (fun x : ℝ => (-2 * c) * x + c ^ 2) F from
      ((iid_int hsupp).const_mul _).add (integrable_const _)),
    integral_add ((iid_int hsupp).const_mul _) (integrable_const _), integral_const_mul, hm, hv]
  simp

lemma Vt_lower (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1)
    (t : ℝ) : exp (-(2 * (|t| * K))) ≤ Vt F t := by
  unfold Vt
  rw [iteratedDeriv_two_cgf_eq_integral (hI hsupp t)]
  set c := deriv (cgf (fun x : ℝ => x) F) t
  have i0 : Integrable (fun x : ℝ => (x - c) ^ 2) F := by simpa using ipow_exp hsupp 2 0 c
  have hA : exp (-(|t| * K)) ≤ ∫ x, (x - c) ^ 2 * exp (t * x) ∂F := by
    calc exp (-(|t| * K)) ≤ exp (-(|t| * K)) * (1 + c ^ 2) :=
          le_mul_of_one_le_right (exp_pos _).le (by nlinarith [sq_nonneg c])
      _ = ∫ x, (x - c) ^ 2 * exp (-(|t| * K)) ∂F := by
          rw [integral_mul_const, sq_int hsupp hm hv c]; ring
      _ ≤ ∫ x, (x - c) ^ 2 * exp (t * x) ∂F :=
          integral_mono_ae (i0.mul_const _) (ipow_exp hsupp 2 t c)
            ((tx_le hsupp t).mono fun x hx => mul_le_mul_of_nonneg_left
              (exp_le_exp.2 (by linarith [neg_abs_le (t * x)])) (sq_nonneg _))
  have hM := mgf_le hsupp t
  have hM1 := one_le_mgf hsupp hm t
  calc exp (-(2 * (|t| * K))) = exp (-(|t| * K)) / exp (|t| * K) := by
        rw [← exp_sub]; ring_nf
    _ ≤ (∫ x, (x - c) ^ 2 * exp (t * x) ∂F) / mgf (fun x : ℝ => x) F t :=
        div_le_div₀ ((exp_pos _).le.trans hA) hA (by linarith) hM

lemma Vt_pos (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (hv : ∫ x, x ^ 2 ∂F = 1)
    (t : ℝ) : 0 < Vt F t := (exp_pos _).trans_le (Vt_lower hsupp hm hv t)

lemma Vt_near (hK : 0 ≤ K) (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0)
    (hv : ∫ x, x ^ 2 ∂F = 1) {t : ℝ} (ht : 2 * (|t| * K) ≤ 1) : |Vt F t - 1| ≤ 4 * K * |t| := by
  have ha : 0 ≤ |t| * K := mul_nonneg (abs_nonneg t) hK
  have hu := Vt_upper hsupp hm hv t
  have hl := Vt_lower hsupp hm hv t
  have e1 := abs_exp_sub_one_le (x := |t| * K) (by rw [abs_of_nonneg ha]; linarith)
  have h2a : (0 : ℝ) ≤ 2 * (|t| * K) := by linarith
  have e2 := abs_exp_sub_one_le (x := -(2 * (|t| * K))) (by
    rw [abs_neg, abs_of_nonneg h2a]; exact ht)
  rw [abs_of_nonneg ha] at e1
  rw [abs_neg, abs_of_nonneg h2a] at e2
  rw [abs_le] at e1 e2 ⊢
  constructor <;> nlinarith

lemma hasDerivAt_mut (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (t : ℝ) : HasDerivAt (tmean F) (Vt F t) t := by
  have ha : AnalyticAt ℝ (cgf (fun x : ℝ => x) F) t := analyticAt_cgf (hI hsupp t)
  have hd := ha.deriv.differentiableAt.hasDerivAt
  unfold Vt tmean
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact hd

lemma mut_zero (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) : tmean F 0 = 0 := by
  unfold tmean
  rw [deriv_cgf_zero (hI hsupp 0)]
  simp [hm]

lemma continuous_mut (hsupp : ∀ᵐ x ∂F, |x| ≤ K) : Continuous (tmean F) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_mut hsupp x).continuousAt

lemma mut_mvt (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) {t : ℝ} (ht : 0 < t) :
    ∃ u ∈ Ioo 0 t, tmean F t = Vt F u * t := by
  obtain ⟨u, hu, e⟩ := exists_hasDerivAt_eq_slope (tmean F) (Vt F) ht
    (fun x _ => (hasDerivAt_mut hsupp x).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_mut hsupp x)
  refine ⟨u, hu, ?_⟩
  rw [e, mut_zero hsupp hm, sub_zero, sub_zero, div_mul_cancel₀ _ ht.ne']

lemma cgf_mvt (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) {t : ℝ} (ht : 0 < t) :
    ∃ u ∈ Ioo 0 t, cgf (fun x : ℝ => x) F t = Vt F u * t ^ 2 / 2 :=
  exists_cgf_eq_iteratedDeriv_two_cgf_mul ht hm (fun x _ => hI hsupp x)

/-- Cumulant estimates on `(0, 1/(2K)]`. -/
theorem cum_near (hK : 0 ≤ K) (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0)
    (hv : ∫ x, x ^ 2 ∂F = 1) {t : ℝ} (ht : 0 < t) (htK : 2 * (t * K) ≤ 1) :
    |tmean F t - t| ≤ 4 * K * t ^ 2 ∧
    |cgf (fun x : ℝ => x) F t - t ^ 2 / 2| ≤ 2 * K * t ^ 3 ∧
    |cgf (fun x : ℝ => x) F t - t * tmean F t + tmean F t ^ 2 / 2| ≤ 14 * K * t ^ 3 := by
  obtain ⟨u1, hu1, e1⟩ := cgf_mvt hsupp hm ht
  obtain ⟨u2, hu2, e2⟩ := mut_mvt hsupp hm ht
  have hb : ∀ u ∈ Ioo 0 t, |Vt F u - 1| ≤ 4 * K * t := fun u hu => by
    have h := Vt_near hK hsupp hm hv (t := u) (by
      rw [abs_of_pos hu.1]; nlinarith [hu.2])
    rw [abs_of_pos hu.1] at h
    exact h.trans (by nlinarith [hu.2])
  have b1 := hb u1 hu1
  have b2 := hb u2 hu2
  have ht2 : 0 < t ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [e2, show Vt F u2 * t - t = (Vt F u2 - 1) * t by ring, abs_mul, abs_of_pos ht]
    nlinarith
  · rw [e1, show Vt F u1 * t ^ 2 / 2 - t ^ 2 / 2 = (Vt F u1 - 1) * (t ^ 2 / 2) by ring, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < t ^ 2 / 2)]
    nlinarith
  · rw [e1, e2]
    have e : Vt F u1 * t ^ 2 / 2 - t * (Vt F u2 * t) + (Vt F u2 * t) ^ 2 / 2 =
        t ^ 2 * ((Vt F u1 - 1) / 2 - (Vt F u2 - 1) + (Vt F u2 - 1) * (Vt F u2 + 1) / 2) := by ring
    rw [e, abs_mul, abs_of_pos ht2]
    have hK4 : 4 * K * t ≤ 2 := by nlinarith
    have hV2 : |Vt F u2 + 1| ≤ 4 := by
      rw [abs_le] at b2 ⊢; constructor <;> nlinarith
    have hbd : |(Vt F u2 - 1) * (Vt F u2 + 1)| ≤ 4 * K * t * 4 := by
      rw [abs_mul]
      exact mul_le_mul b2 hV2 (abs_nonneg _) (by nlinarith [abs_nonneg (Vt F u2 - 1)])
    have hx : |(Vt F u1 - 1) / 2 - (Vt F u2 - 1) + (Vt F u2 - 1) * (Vt F u2 + 1) / 2| ≤
        14 * K * t := by
      rw [abs_le] at b1 b2 hbd ⊢
      constructor <;> nlinarith
    calc t ^ 2 * |_| ≤ t ^ 2 * (14 * K * t) := mul_le_mul_of_nonneg_left hx ht2.le
      _ = 14 * K * t ^ 3 := by ring

end IidA

end P99bcb804

end X60_IidA

section X61_IidB

/-! E (iid Cramér) part B: the Esscher tilt of a product law, change of measure. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace P99bcb804

section IidB

variable {ι : Type} [Fintype ι]

/-- A product of densities is the density of the product. -/
lemma pi_wd (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ → ℝ≥0∞) (hρ : Measurable ρ)
    [IsProbabilityMeasure (μ.withDensity ρ)] :
    Measure.pi (fun _ : ι => μ.withDensity ρ) =
      (Measure.pi fun _ : ι => μ).withDensity (fun x => ∏ i, ρ (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have e : (univ.pi s).indicator (fun x : ι → ℝ => ∏ i, ρ (x i)) =
      fun x => ∏ i, (s i).indicator ρ (x i) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [e, lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : ι → ℝ) => (s i).indicator ρ (x i))
    (iIndepFun_pi (μ := fun _ : ι => μ) (X := fun i => (s i).indicator ρ)
      (fun i => (hρ.indicator (hs i)).aemeasurable))
    (fun i => (hρ.indicator (hs i)).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  exact (measurePreserving_eval (fun _ : ι => μ) i).lintegral_comp (hρ.indicator (hs i))

variable {F : Measure ℝ} [IsProbabilityMeasure F] {K : ℝ}

/-- The Esscher tilt `e^{hx} F(dx) / M(h)`. -/
noncomputable def Ft (F : Measure ℝ) (h : ℝ) : Measure ℝ := F.tilted (fun x => h * x)

lemma Ft_prob (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (h : ℝ) : IsProbabilityMeasure (Ft F h) :=
  isProbabilityMeasure_tilted (iexp hsupp h)

lemma Ft_ae (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (h : ℝ) : ∀ᵐ x ∂(Ft F h), |x| ≤ K :=
  (tilted_absolutelyContinuous F _).ae_le hsupp

lemma Ft_mean (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (h : ℝ) : ∫ x, x ∂(Ft F h) = tmean F h :=
  integral_tilted_mul_self (X := fun x : ℝ => x) (hI hsupp h)

lemma Ft_var (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (h : ℝ) :
    ∫ x, (x - tmean F h) ^ 2 ∂(Ft F h) = Vt F h := by
  have := Ft_prob hsupp h
  have hv := variance_tilted_mul (X := fun x : ℝ => x) (μ := F) (hI hsupp h)
  rw [variance_eq_integral (by fun_prop : AEMeasurable (fun x : ℝ => x) _)] at hv
  have e := Ft_mean hsupp h
  unfold Ft at e ⊢
  simp only [id] at hv
  rw [e] at hv
  exact hv

lemma tmean_abs (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (h : ℝ) : |tmean F h| ≤ K := by
  have := Ft_prob hsupp h
  rw [← Ft_mean hsupp h]
  have := norm_integral_le_of_norm_le_const (μ := Ft F h) (f := fun x : ℝ => x)
    ((Ft_ae hsupp h).mono fun x hx => by rwa [Real.norm_eq_abs])
  simpa using this

/-- Change of measure to the tilted product law. -/
lemma com (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0) (h : ℝ) {A : Set (ι → ℝ)}
    (hA : MeasurableSet A) :
    (Measure.pi fun _ : ι => F).real A =
      ∫ x, A.indicator (fun x : ι → ℝ =>
        mgf (fun y : ℝ => y) F h ^ Fintype.card ι * exp (-(h * ∑ i, x i))) x
        ∂(Measure.pi fun _ : ι => Ft F h) := by
  set M := mgf (fun y : ℝ => y) F h with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (one_le_mgf hsupp hm h)
  set ρ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (exp (h * x) / M) with hρdef
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hFt : Ft F h = F.withDensity ρ := rfl
  have : IsProbabilityMeasure (F.withDensity ρ) := hFt ▸ Ft_prob hsupp h
  rw [hFt, pi_wd F ρ hρ, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x : ι → ℝ => ∏ i, ρ (x i)) from
      Finset.measurable_prod _ fun i _ => hρ.comp (measurable_pi_apply i))
    (ae_of_all _ fun x => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top)]
  have e : ∀ x : ι → ℝ, (∏ i, ρ (x i)).toReal • A.indicator (fun x : ι → ℝ =>
      M ^ Fintype.card ι * exp (-(h * ∑ i, x i))) x = A.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, smul_eq_mul, ENNReal.toReal_prod]
      simp only [hρdef, ENNReal.toReal_ofReal (div_pos (exp_pos _) hM).le]
      rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
        ← Finset.mul_sum]
      have hMm : M ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hM.ne'
      rw [div_mul_eq_mul_div, mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one,
        div_self hMm]
    · simp [Set.indicator_of_notMem hx]
  simp_rw [e]
  rw [integral_indicator_const _ hA, smul_eq_mul, mul_one]

end IidB

end P99bcb804

end X61_IidB

section X62_IidB2

/-! E (iid Cramér) part B2: Berry–Esseen under the tilted product law, Laplace form. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace P99bcb804

section LapBE

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Laplace functional of a bounded independent sum is within `14 δ` of the Gaussian value. -/
theorem lap_BE (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P) (hmeas : ∀ i, Measurable (ξ i)) {δ : ℝ}
    (hδ : 0 < δ) (hb : ∀ i ω, |ξ i ω| ≤ δ) (h0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    (h1 : ∑ i, ∫ ω, ξ i ω ^ 2 ∂P = 1) (hδ1 : δ ≤ 1) {u : ℝ} (hu : 0 ≤ u) :
    |∫ ω, lapG u (∑ i, ξ i ω) ∂P - exp (u ^ 2 / 2) * (1 - Phi u)| ≤ 14 * δ := by
  set W : Ω → ℝ := fun ω => ∑ i, ξ i ω with hW
  have hWm : Measurable W := Finset.measurable_sum _ fun i _ => hmeas i
  have : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hWm.aemeasurable
  have hmap : ∫ ω, lapG u (W ω) ∂P = ∫ w, lapG u w ∂(P.map W) :=
    (integral_map hWm.aemeasurable (measurable_lapG u).aestronglyMeasurable).symm
  rw [hmap, ← lap_gauss u]
  have hlt : ∀ c, |(P.map W).real (Iio c) - (gaussianReal 0 1).real (Iio c)| ≤ 7 * δ := by
    intro c
    rw [gauss_Iio, measureReal_def, Measure.map_apply hWm measurableSet_Iio]
    exact bdd_BE ξ hind hmeas hδ hb h0 h1 hδ1 c
  have hle : |(P.map W).real (Iic 0) - (gaussianReal 0 1).real (Iic 0)| ≤ 7 * δ := by
    have hneg := bdd_BE (fun i ω => -ξ i ω)
      (hind.comp (fun _ x => -x) (fun _ => measurable_neg)) (fun i => (hmeas i).neg) hδ
      (fun i ω => by rw [abs_neg]; exact hb i ω)
      (fun i => by rw [integral_neg, h0, neg_zero])
      (by simpa only [neg_sq] using h1) hδ1 0
    have g0 : (gaussianReal 0 1).real (Iic 0) = Phi 0 := by rw [Phi, cdf_eq_real]
    rw [g0, measureReal_def, Measure.map_apply hWm measurableSet_Iic]
    have hc : {ω | ∑ i, -ξ i ω < 0} = (W ⁻¹' Iic 0)ᶜ := by
      ext ω; simp [hW, Finset.sum_neg_distrib]
    rw [hc, prob_compl_eq_one_sub (hWm measurableSet_Iic),
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one] at hneg
    rw [Phi_zero] at hneg ⊢
    rw [abs_le] at hneg ⊢; constructor <;> linarith [hneg.1, hneg.2]
  have := lap_cmp (P.map W) (gaussianReal 0 1) hlt hle hu
  linarith [this, le_abs_self (∫ w, lapG u w ∂(P.map W) - ∫ w, lapG u w ∂(gaussianReal 0 1))]

end LapBE

section TiltIid

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Measure ℝ} [IsProbabilityMeasure F] {K : ℝ}

noncomputable def clampK (K y : ℝ) : ℝ := max (-K) (min K y)

lemma clampK_eq {K y : ℝ} (hy : |y| ≤ K) : clampK K y = y := by
  unfold clampK; rw [abs_le] at hy; rw [min_eq_right hy.2, max_eq_right hy.1]

lemma clampK_abs {K : ℝ} (hK : 0 ≤ K) (y : ℝ) : |clampK K y| ≤ K := by
  unfold clampK; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma measurable_clampK (K : ℝ) : Measurable (clampK K) := by
  unfold clampK; fun_prop

omit [DecidableEq ι] in
lemma int_eval (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : ι) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ x, g (x i) ∂(Measure.pi fun _ : ι => μ) = ∫ y, g y ∂μ := by
  have := integral_map (μ := Measure.pi fun _ : ι => μ) (φ := fun x : ι → ℝ => x i)
    (measurable_pi_apply i).aemeasurable (f := g) hg.aestronglyMeasurable
  rw [(measurePreserving_eval (fun _ : ι => μ) i).map_eq] at this
  exact this.symm

/-- Tilted iid tail: exact Cramér prefactor times the Gaussian Laplace value, error `14 δ`. -/
theorem tilt_iid (hK : 0 < K) (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0)
    (hv : ∫ x, x ^ 2 ∂F = 1) {h : ℝ} (hh : 0 ≤ h) (hc : 0 < Fintype.card ι)
    (hδ1 : 2 * K / √(Fintype.card ι * Vt F h) ≤ 1) :
    |(Measure.pi fun _ : ι => F).real {x | Fintype.card ι * tmean F h < ∑ i, x i}
      - mgf (fun y : ℝ => y) F h ^ Fintype.card ι * exp (-(h * (Fintype.card ι * tmean F h)))
        * (exp ((h * √(Fintype.card ι * Vt F h)) ^ 2 / 2)
            * (1 - Phi (h * √(Fintype.card ι * Vt F h))))|
      ≤ mgf (fun y : ℝ => y) F h ^ Fintype.card ι * exp (-(h * (Fintype.card ι * tmean F h)))
        * (14 * (2 * K / √(Fintype.card ι * Vt F h))) := by
  have := Ft_prob hsupp h
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  set μ := tmean F h with hμ
  set σ := √(m * Vt F h) with hσdef
  set t := m * μ with ht
  set u := h * σ with hu
  set δ := 2 * K / σ with hδdef
  have hV := Vt_pos hsupp hm hv h
  have hm0 : (0:ℝ) < m := by rw [hmdef]; exact_mod_cast hc
  have hσ : 0 < σ := Real.sqrt_pos.mpr (mul_pos hm0 hV)
  have hσ2 : σ ^ 2 = m * Vt F h := Real.sq_sqrt (mul_pos hm0 hV).le
  have hδ : 0 < δ := div_pos (by linarith) hσ
  have hA : MeasurableSet {x : ι → ℝ | t < ∑ i, x i} :=
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  rw [com hsupp hm h hA]
  set M := mgf (fun y : ℝ => y) F h with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (one_le_mgf hsupp hm h)
  have hC : 0 ≤ M ^ Fintype.card ι * exp (-(h * t)) := by positivity
  have e1 : ∀ x : ι → ℝ, {x : ι → ℝ | t < ∑ i, x i}.indicator
      (fun x => M ^ Fintype.card ι * exp (-(h * ∑ i, x i))) x
      = M ^ Fintype.card ι * exp (-(h * t)) * lapG u ((∑ i, x i - t) / σ) := by
    intro x
    unfold lapG
    by_cases hx : t < ∑ i, x i
    · rw [Set.indicator_of_mem (show x ∈ {x : ι → ℝ | t < ∑ i, x i} from hx),
        if_pos (div_pos (by linarith) hσ), mul_assoc, ← exp_add]
      congr 2; rw [hu]; field_simp; ring
    · rw [Set.indicator_of_notMem (show x ∉ {x : ι → ℝ | t < ∑ i, x i} from hx), if_neg, mul_zero]
      rw [not_lt]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hσ.le
  simp_rw [e1]
  rw [integral_const_mul, ← mul_sub, abs_mul, abs_of_nonneg hC]
  refine mul_le_mul_of_nonneg_left ?_ hC
  set ξ : ι → (ι → ℝ) → ℝ := fun i x => (clampK K (x i) - μ) / σ with hξ
  have hae : ∀ᵐ x ∂(Measure.pi fun _ : ι => Ft F h), ∀ i, |x i| ≤ K :=
    ae_all_iff.mpr fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => Ft F h)
      (i := i)).eventually (p := fun y : ℝ => |y| ≤ K) (Ft_ae hsupp h)
  have hcong : ∫ x, lapG u ((∑ i, x i - t) / σ) ∂(Measure.pi fun _ : ι => Ft F h)
      = ∫ x, lapG u (∑ i, ξ i x) ∂(Measure.pi fun _ : ι => Ft F h) := by
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    show lapG u ((∑ i, x i - t) / σ) = lapG u (∑ i, (clampK K (x i) - μ) / σ)
    congr 1
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [clampK_eq (hx _), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ht, hmdef]
  rw [hcong]
  have hμK : |μ| ≤ K := tmean_abs hsupp h
  have hclm := measurable_clampK K
  have hgm : Measurable (fun y : ℝ => (clampK K y - μ) / σ) :=
    (hclm.sub measurable_const).div_const σ
  have hclae : ∀ᵐ y ∂(Ft F h), clampK K y = y := (Ft_ae hsupp h).mono fun y hy => clampK_eq hy
  have hint : Integrable (fun y : ℝ => y) (Ft F h) :=
    int_of_ae_bdd (F := Ft F h) (g := fun y : ℝ => y) measurable_id K (Ft_ae hsupp h)
  refine lap_BE ξ ?_ (fun i => hgm.comp (measurable_pi_apply i)) hδ ?_ ?_ ?_ hδ1 (by positivity)
  · exact iIndepFun_pi (μ := fun _ : ι => Ft F h) (X := fun _ y => (clampK K y - μ) / σ)
      (fun _ => hgm.aemeasurable)
  · intro i x
    simp only [hξ]
    rw [abs_div, abs_of_pos hσ]
    refine div_le_div_of_nonneg_right ?_ hσ.le
    have := clampK_abs hK.le (x i)
    calc |clampK K (x i) - μ| ≤ |clampK K (x i)| + |μ| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  · intro i
    refine (int_eval (Ft F h) i hgm).trans ?_
    rw [integral_congr_ae (g := fun y : ℝ => (y - μ) / σ) (hclae.mono fun y hy => by simp only [hy]),
      integral_div, integral_sub hint (integrable_const μ), integral_const, Ft_mean hsupp h, ← hμ]
    simp
  · have e2 : ∀ i, ∫ x, ξ i x ^ 2 ∂(Measure.pi fun _ : ι => Ft F h) = Vt F h / σ ^ 2 := by
      intro i
      refine (int_eval (Ft F h) i (g := fun y => ((clampK K y - μ) / σ) ^ 2)
        (hgm.pow_const 2)).trans ?_
      rw [integral_congr_ae (g := fun y : ℝ => (y - μ) ^ 2 / σ ^ 2)
        (hclae.mono fun y hy => by simp only [hy, div_pow]), integral_div, Ft_var hsupp h]
    rw [Finset.sum_congr rfl fun i _ => e2 i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hσ2, ← hmdef]
    field_simp

end TiltIid

end P99bcb804

end X62_IidB2

section X63_IidC

/-! E (iid Cramér) part C: saddle_iid point and the two-sided Cramér estimate for iid sums
(KMT 1976 II, used for the root of the dyadic scheme; Petrov's form for bounded summands). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace P99bcb804

section IidC

variable {F : Measure ℝ} [IsProbabilityMeasure F] {K : ℝ}

/-- Saddle point: `tmean F h = τ` with `0 < h ≤ 2 τ`. -/
lemma saddle_iid (hK : 0 < K) (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0)
    (hv : ∫ x, x ^ 2 ∂F = 1) {τ : ℝ} (hτ : 0 < τ) (hτK : 16 * K * τ ≤ 1) :
    ∃ h, 0 < h ∧ h ≤ 2 * τ ∧ tmean F h = τ := by
  have h2 : 0 < 2 * τ := by linarith
  have hc := (cum_near hK.le hsupp hm hv h2 (by nlinarith)).1
  have hge : τ ≤ tmean F (2 * τ) := by
    rw [abs_le] at hc
    nlinarith [hc.1, mul_nonneg hτ.le (sub_nonneg.2 hτK)]
  have h0 : tmean F 0 = 0 := mut_zero hsupp hm
  obtain ⟨h, hh, he⟩ := intermediate_value_Icc h2.le (continuous_mut hsupp).continuousOn
    (show τ ∈ Icc (tmean F 0) (tmean F (2 * τ)) from ⟨by rw [h0]; exact hτ.le, hge⟩)
  refine ⟨h, ?_, hh.2, he⟩
  rcases hh.1.eq_or_lt with h0' | hp
  · rw [← h0', h0] at he; linarith
  · exact hp

lemma abs_sqrt_sub_one {V : ℝ} (hV : 0 ≤ V) : |√V - 1| ≤ |V - 1| := by
  have e : V - 1 = (√V - 1) * (√V + 1) := by
    have := Real.sq_sqrt hV
    linear_combination -this
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < √V + 1)]
  nlinarith [abs_nonneg (√V - 1), mul_nonneg (abs_nonneg (√V - 1)) (Real.sqrt_nonneg V)]

set_option maxHeartbeats 1000000 in
/-- Two-sided Cramér estimate for the right tail of an iid bounded sum. -/
theorem iid_cramer_right (hK : 0 < K) (hsupp : ∀ᵐ x ∂F, |x| ≤ K) (hm : ∫ x, x ∂F = 0)
    (hv : ∫ x, x ^ 2 ∂F = 1) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι], 1 ≤ Fintype.card ι →
      ∀ y : ℝ, √(Fintype.card ι : ℝ) ≤ y → y ≤ ε * Fintype.card ι →
        (Measure.pi fun _ : ι => F).real {x | y < ∑ i, x i} ≤
            (1 - Phi (y / √(Fintype.card ι : ℝ))) *
              exp (c * (y ^ 3 / (Fintype.card ι : ℝ) ^ 2)) ∧
        (1 - Phi (y / √(Fintype.card ι : ℝ))) *
            exp (-(c * (y ^ 3 / (Fintype.card ι : ℝ) ^ 2))) ≤
          (Measure.pi fun _ : ι => F).real {x | y < ∑ i, x i} := by
  set A : ℝ := 56 * K * √(2 * π) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨1248 * K + 130 * A, min (1 / (16 * K)) (1 / (130 * A)), by positivity,
    by positivity, ?_⟩
  intro ι _ _ hc y hys hyε
  set ε := min (1 / (16 * K)) (1 / (130 * A)) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / (16 * K) := min_le_left _ _
  have hε2 : ε ≤ 1 / (130 * A) := min_le_right _ _
  have hKε : K * ε ≤ 1 / 16 := by
    calc K * ε ≤ K * (1 / (16 * K)) := mul_le_mul_of_nonneg_left hε1 hK.le
      _ = 1 / 16 := by field_simp
  have hAε : A * ε ≤ 1 / 130 := by
    calc A * ε ≤ A * (1 / (130 * A)) := mul_le_mul_of_nonneg_left hε2 hA0.le
      _ = 1 / 130 := by field_simp
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  have hm1 : (1:ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hc
  have hm0 : 0 < m := by linarith
  set s := √m with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hm0
  have hs2 : s ^ 2 = m := Real.sq_sqrt hm0.le
  have hy0 : 0 < y := lt_of_lt_of_le hs0 hys
  set τ := y / m with hτdef
  set x := y / s with hxdef
  have hmτ : m * τ = y := by rw [hτdef]; field_simp
  have hsτ : s * τ = x := by rw [hτdef, hxdef, ← hs2]; field_simp
  have hx1 : 1 ≤ x := by rw [hxdef, le_div_iff₀ hs0]; linarith
  have hx0 : 0 ≤ x := by linarith
  have hτ0 : 0 < τ := div_pos hy0 hm0
  have hτε : τ ≤ ε := by rw [hτdef, div_le_iff₀ hm0]; linarith
  have hY : y ^ 3 / m ^ 2 = τ * x ^ 2 := by
    rw [hτdef, hxdef, div_pow, ← hs2]; field_simp
  rw [hY]
  set Y := τ * x ^ 2 with hYdef
  have hτY : τ ≤ Y := le_mul_of_one_le_right hτ0.le (one_le_pow₀ hx1)
  have hxx : x ≤ x ^ 2 := by rw [sq]; exact le_mul_of_one_le_right hx0 hx1
  have hτx : τ * x ≤ Y := mul_le_mul_of_nonneg_left hxx hτ0.le
  have hinv : 1 / s ≤ τ := by
    rw [div_le_iff₀ hs0, mul_comm, hsτ]; exact hx1
  have hτK : 16 * K * τ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hτε hK.le; linarith
  obtain ⟨h, hh0, hh2, hmean⟩ := saddle_iid hK hsupp hm hv hτ0 hτK
  have hhK0 := mul_le_mul_of_nonneg_right hh2 hK.le
  have hhK : 2 * (h * K) ≤ 1 := by linarith
  have hcum := cum_near hK.le hsupp hm hv hh0 hhK
  rw [hmean] at hcum
  obtain ⟨hc1, -, hc3⟩ := hcum
  have hVn := Vt_near hK.le hsupp hm hv (t := h) (by rw [abs_of_pos hh0]; exact hhK)
  rw [abs_of_pos hh0] at hVn
  set V := Vt F h with hVdef
  have hVab := abs_le.1 hVn
  have hhKs : K * h ≤ 1 / 8 := by linarith
  have hV14 : 1 / 4 ≤ V := by linarith [hVab.1]
  have hV4 : V ≤ 4 := by linarith [hVab.2]
  have hV0 : 0 < V := by linarith
  have hsV1 : 1 / 2 ≤ √V := Real.le_sqrt_of_sq_le (by linarith)
  have hsV2 : √V ≤ 2 := (Real.sqrt_le_sqrt hV4).trans_eq
    (by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)])
  set σ := √(m * V) with hσdef
  have hσs : σ = s * √V := by rw [hσdef, Real.sqrt_mul hm0.le]
  have hσ0 : 0 < σ := by rw [hσs]; positivity
  have hσlow : s / 2 ≤ σ := by
    rw [hσs]; have := mul_le_mul_of_nonneg_left hsV1 hs0.le; linarith
  have hδ : 2 * K / σ ≤ 4 * K * τ := by
    rw [div_le_iff₀ hσ0, hσs]
    have h1 : 1 / 2 ≤ τ * (s * √V) := by
      have : τ * (s * √V) = x * √V := by rw [← hsτ]; ring
      rw [this]
      have := mul_le_mul hx1 hsV1 (by norm_num) hx0
      linarith
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * K)
    linarith
  have hδ1 : 2 * K / σ ≤ 1 := hδ.trans (by linarith)
  have hcard : 0 < Fintype.card ι := by omega
  have key := tilt_iid (ι := ι) hK hsupp hm hv hh0.le hcard hδ1
  rw [hmean, ← hmdef, hmτ, ← hVdef, ← hσdef] at key
  have hMpos : 0 < mgf (fun y : ℝ => y) F h := lt_of_lt_of_le one_pos (one_le_mgf hsupp hm h)
  set L0 := m * cgf (fun y : ℝ => y) F h - h * y with hL0def
  have hE : mgf (fun y : ℝ => y) F h ^ Fintype.card ι * exp (-(h * y)) = exp L0 := by
    rw [hL0def, sub_eq_add_neg, exp_add, hmdef, Real.exp_nat_mul, cgf, Real.exp_log hMpos]
  rw [hE] at key
  set u := h * σ with hudef
  set ψu := exp (u ^ 2 / 2) * (1 - Phi u) with hψu
  have hψ : 0 < ψu := mul_pos (exp_pos _) (one_sub_Phi_pos u)
  set r := 14 * (2 * K / σ) / ψu with hr
  have hrψ : r * ψu = 14 * (2 * K / σ) := div_mul_cancel₀ _ hψ.ne'
  have hr0 : 0 ≤ r := by positivity
  have hP : |(Measure.pi fun _ : ι => F).real {x | y < ∑ i, x i} - exp L0 * ψu| ≤
      exp L0 * (r * ψu) := by rw [hrψ]; exact key
  -- geometry of u and x
  have hu0 : 0 ≤ u := by positivity
  have hu4 : u ≤ 4 * x := by
    rw [hudef, hσs, ← hsτ]
    have : h * (s * √V) ≤ (2 * τ) * (s * 2) :=
      mul_le_mul hh2 (mul_le_mul_of_nonneg_left hsV2 hs0.le) (by positivity) (by linarith)
    linarith
  have hsq1 : |√V - 1| ≤ 4 * K * h := (abs_sqrt_sub_one hV0.le).trans hVn
  have hhτ : |h * √V - τ| ≤ 8 * K * h ^ 2 := by
    have e : h * √V - τ = h * (√V - 1) + (h - τ) := by ring
    rw [e]
    have a1 : |h * (√V - 1)| ≤ h * (4 * K * h) := by
      rw [abs_mul, abs_of_pos hh0]; exact mul_le_mul_of_nonneg_left hsq1 hh0.le
    have a2 : |h - τ| ≤ 4 * K * h ^ 2 := by rw [abs_sub_comm]; exact hc1
    calc |h * (√V - 1) + (h - τ)| ≤ |h * (√V - 1)| + |h - τ| := abs_add_le _ _
      _ ≤ 8 * K * h ^ 2 := by linarith
  have hh2sq : h ^ 2 ≤ 4 * τ ^ 2 := by
    have := pow_le_pow_left₀ hh0.le hh2 2
    linarith [show (2 * τ) ^ 2 = 4 * τ ^ 2 by ring]
  have hux : |u - x| ≤ 32 * K * (τ * x) := by
    have e : u - x = s * (h * √V - τ) := by rw [hudef, hσs, ← hsτ]; ring
    rw [e, abs_mul, abs_of_pos hs0]
    calc s * |h * √V - τ| ≤ s * (8 * K * h ^ 2) := mul_le_mul_of_nonneg_left hhτ hs0.le
      _ ≤ s * (8 * K * (4 * τ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh2sq (by positivity)) hs0.le
      _ = 32 * K * ((s * τ) * τ) := by ring
      _ = 32 * K * (τ * x) := by rw [hsτ]; ring
  have hKY : 0 ≤ K * Y := by positivity
  have hτx0 : 0 ≤ τ * x := by positivity
  have hsq : |(u ^ 2 - x ^ 2) / 2| ≤ 80 * K * Y := by
    rw [show (u ^ 2 - x ^ 2) / 2 = (u - x) * ((u + x) / 2) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (u + x) / 2)]
    calc |u - x| * ((u + x) / 2) ≤ 32 * K * (τ * x) * (5 * x / 2) :=
          mul_le_mul hux (by linarith) (by positivity) (by positivity)
      _ = 80 * K * Y := by rw [hYdef]; ring
  have hHzx : |Hz x * (u - x)| ≤ 544 * K * Y := by
    rw [abs_mul, abs_of_pos (Hz_pos x)]
    have hz := Hz_le_lin hx0
    calc Hz x * |u - x| ≤ (1 + 16 * x) * (32 * K * (τ * x)) :=
          mul_le_mul hz hux (abs_nonneg _) (by positivity)
      _ = 32 * K * (τ * x) + 512 * K * Y := by rw [hYdef]; ring
      _ ≤ 544 * K * Y := by
          have := mul_le_mul_of_nonneg_left hτx (by positivity : (0:ℝ) ≤ 32 * K); linarith
  have hsq2 : 8 * (u - x) ^ 2 ≤ 512 * K * Y := by
    have a : (u - x) ^ 2 ≤ (32 * K * (τ * x)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hux 2
    have b : (32 * K * (τ * x)) ^ 2 = 1024 * K * (K * τ) * Y := by rw [hYdef]; ring
    have c : K * τ ≤ 1 / 16 := (mul_le_mul_of_nonneg_left hτε hK.le).trans hKε
    have d : 1024 * K * (K * τ) * Y ≤ 1024 * K * (1 / 16) * Y := by
      have := mul_le_mul_of_nonneg_left c (by positivity : 0 ≤ 1024 * K)
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  have hL0 : |L0 + x ^ 2 / 2| ≤ 112 * K * Y := by
    have e : L0 + x ^ 2 / 2 =
        m * (cgf (fun y : ℝ => y) F h - h * τ + τ ^ 2 / 2) := by
      rw [hL0def, ← hmτ, ← hsτ, mul_pow, hs2]; ring
    rw [e, abs_mul, abs_of_pos hm0]
    have h3 : h ^ 3 ≤ (2 * τ) ^ 3 := pow_le_pow_left₀ hh0.le hh2 3
    calc m * |cgf (fun y : ℝ => y) F h - h * τ + τ ^ 2 / 2| ≤ m * (14 * K * h ^ 3) :=
          mul_le_mul_of_nonneg_left hc3 hm0.le
      _ ≤ m * (14 * K * (2 * τ) ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ hm0.le
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 112 * K * (m * τ ^ 3) := by ring
      _ = 112 * K * Y := by rw [hYdef, ← hsτ, ← hs2]; ring
  have hr_eq : r = 28 * K * √(2 * π) * Hz u / σ := by
    rw [hr, hψu, psi_eq]; field_simp; ring
  have hr65 : r ≤ 65 * A * τ := by
    have hHz : Hz u ≤ 1 + 64 * x := by have := Hz_le_lin hu0; linarith
    have hHz0 := Hz_pos u
    have st1 : 28 * K * √(2 * π) * Hz u / σ ≤ A * Hz u / s := by
      rw [div_le_div_iff₀ hσ0 hs0, hA]
      have : 0 ≤ 28 * K * √(2 * π) * Hz u := by positivity
      have h2 : s ≤ 2 * σ := by linarith
      have key := mul_le_mul_of_nonneg_left h2 this
      have e : 28 * K * √(2 * π) * Hz u * (2 * σ) = 56 * K * √(2 * π) * Hz u * σ := by ring
      linarith
    have st2 : A * Hz u / s ≤ A * (1 + 64 * x) / s :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHz hA0.le) hs0.le
    have st3 : A * (1 + 64 * x) / s = A * (1 / s) + 64 * A * τ := by
      rw [← hsτ]; field_simp
    have st4 : A * (1 / s) ≤ A * τ := mul_le_mul_of_nonneg_left hinv hA0.le
    rw [hr_eq]; linarith
  have hr1 : r ≤ 1 / 2 := by
    have : A * τ ≤ 1 / 130 := (mul_le_mul_of_nonneg_left hτε hA0.le).trans hAε
    linarith
  have hrY : r ≤ 65 * A * Y := hr65.trans (mul_le_mul_of_nonneg_left hτY (by positivity))
  have hRB := ratio_bounds hx0 hu0
  have hlo : (1 - Phi x) * exp (x ^ 2 / 2) *
      exp ((u ^ 2 - x ^ 2) / 2 - Hz x * (u - x) - 8 * (u - x) ^ 2) ≤ ψu := by
    rw [mul_comm (1 - Phi x)]; exact hRB.1
  have hhi : ψu ≤ (1 - Phi x) * exp (x ^ 2 / 2) *
      exp ((u ^ 2 - x ^ 2) / 2 - Hz x * (u - x)) := by
    rw [mul_comm (1 - Phi x)]; exact hRB.2
  obtain ⟨hL0a, hL0b⟩ := abs_le.1 hL0
  obtain ⟨hsqa, hsqb⟩ := abs_le.1 hsq
  obtain ⟨hHa, hHb⟩ := abs_le.1 hHzx
  have hfin := combine (T := (1248 * K + 130 * A) * Y) hψ (one_sub_Phi_pos x) hP hr0 hr1 hlo hhi
    (by linarith) (by linarith)
  exact ⟨hfin.2, hfin.1⟩

end IidC

end P99bcb804

end X63_IidC

end P99Hyps

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ {F : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure F] {K : ℝ},
      (0 : ℝ) < K →
        (∀ᵐ (x : ℝ) ∂F, |x| ≤ K) →
          ∫ (x : ℝ), x ∂F = (0 : ℝ) →
            ∫ (x : ℝ), x ^ (2 : ℕ) ∂F = (1 : ℝ) →
              ∃ (c : ℝ) (ε : ℝ),
                (0 : ℝ) < c ∧
                  (0 : ℝ) < ε ∧
                    ∀ (ι : Type) [inst : Fintype ι] [DecidableEq ι],
                      (1 : ℕ) ≤ Fintype.card ι →
                        ∀ (y : ℝ),
                          √↑(Fintype.card ι) ≤ y →
                            y ≤ ε * ↑(Fintype.card ι) →
                              MeasureTheory.Measure.real (MeasureTheory.Measure.pi fun (x : ι) => F)
                                    {x : ι → ℝ | y < ∑ i : ι, x i} ≤
                                  ((1 : ℝ) -
                                      (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                        (y / √↑(Fintype.card ι))) *
                                    Real.exp (c * (y ^ (3 : ℕ) / ↑(Fintype.card ι) ^ (2 : ℕ))) ∧
                                ((1 : ℝ) -
                                      (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                        (y / √↑(Fintype.card ι))) *
                                    Real.exp (-(c * (y ^ (3 : ℕ) / ↑(Fintype.card ι) ^ (2 : ℕ)))) ≤
                                  MeasureTheory.Measure.real (MeasureTheory.Measure.pi fun (x : ι) => F)
                                    {x : ι → ℝ | y < ∑ i : ι, x i} := by
  first
  | exact P99bcb804.iid_cramer_right
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.iid_cramer_right <;> assumption)
