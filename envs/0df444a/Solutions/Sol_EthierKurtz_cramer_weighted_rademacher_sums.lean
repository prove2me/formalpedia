-- Prove2me | solution 1 for EthierKurtz.cramer_weighted_rademacher_sums
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:55:06.650561+00:00
-- url     : https://prove2.me/submissions/e18b5040-bb0b-4293-b0aa-bcbd612c3387

import Mathlib
import Theorems.Thm_EthierKurtz_berry_esseen_bounded_independent

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section P99Hyps
section X11_Cr3

/-! R4 / Cr3: smoothed cumulant functions, saddle point, Legendre expansion.
`Ls G σ t = cgf t + t²σ²/2` (cgf of `G ∗ N(0,σ²)`), `L1s = Ls'`, `L2s = Ls''`.
* `L1s_mono`: `L1s` increases at rate `≥ 1/2` on `[-t1,t1]`; `saddle`: `L1s t = c` solvable for `|c| ≤ t1/2`, `|t| ≤ 2|c|`;
* `Ls_taylor`: Taylor bounds; `leg_at`: Legendre expansion of `Λ(t) = t L1s t - Ls t`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def L2s (G : Measure ℝ) (σ t : ℝ) : ℝ :=
  iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t + σ ^ 2

section Cr3

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

end Cr3

end P99bcb804

end X11_Cr3

section X13_Nd1

/-! R4 / Nd1 (Q5 node, near region): ratio of the smoothed density at `N(c±δ)` to `N c`.
`near_ratio`: `f(N(c+δ)) f(N(c-δ)) = f(Nc)² exp(-Nδ²/L2s tc) exp(±K(1/√N + |δ| + N|δ|³))`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

/-- density of the smoothed iid sum `Σ_ι G + N(0, card·σ²)` at `a`. -/
noncomputable def fS (G : Measure ℝ) (ι : Type) [Fintype ι] (σ a : ℝ) : ℝ :=
  ∫ y, gaussianPDFReal 0 (Fintype.card ι * σ ^ 2).toNNReal (a - y)
    ∂((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i))

section Nd1

end Nd1

end P99bcb804

end X13_Nd1

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

section X23_Nd5

/-! R4 / Nd5: the standardised conditional density of the half-difference given the total.
`ffN x = fS(Nc + s x/2) fS(Nc - s x/2)`, `s = √(2N L2s tc)`, `hN = ffN / ZN`. Integrability,
`near_x` (near bounds in the `x` variable) and `ZN_low` (`ZN ≥ 2 fS(Nc)² e^{-1}`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def sN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ tc : ℝ) : ℝ :=
  √(2 * Fintype.card ι * L2s G σ tc)

noncomputable def ffN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc x : ℝ) : ℝ :=
  fS G ι σ (Fintype.card ι * c + sN G ι σ tc * x / 2) *
    fS G ι σ (Fintype.card ι * c - sN G ι σ tc * x / 2)

noncomputable def ZN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc : ℝ) : ℝ :=
  ∫ x, ffN G ι σ c tc x

noncomputable def hN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc x : ℝ) : ℝ :=
  ffN G ι σ c tc x / ZN G ι σ c tc

section Nd5

variable {G : Measure ℝ} [IsProbabilityMeasure G]

end Nd5

end P99bcb804

end X23_Nd5

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

/-- sign of a Bool: `false ↦ 1`, `true ↦ -1`. -/
def sg (b : Bool) : ℝ := if b then -1 else 1

/-- tilted Bernoulli weights `e^{a s}/(2 cosh a)`. -/
noncomputable def tw (a : ℝ) (b : Bool) : ℝ := exp (a * sg b) / (2 * cosh a)

lemma tw_pos (a : ℝ) (b : Bool) : 0 < tw a b := by
  unfold tw; have := cosh_pos a; positivity

lemma tw_false (a : ℝ) : tw a false = (1 + tanh a) / 2 := by
  unfold tw sg
  have hc := cosh_pos a
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq] at *
  simp only [Bool.false_eq_true, if_false, mul_one]
  field_simp
  ring

lemma tw_true (a : ℝ) : tw a true = (1 - tanh a) / 2 := by
  unfold tw sg
  have hc := cosh_pos a
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq] at *
  simp only [if_true, mul_neg, mul_one]
  field_simp
  ring

/-- tilted Bernoulli measure on `Bool`. -/
noncomputable def tb (a : ℝ) : Measure Bool :=
  ENNReal.ofReal (tw a false) • Measure.dirac false + ENNReal.ofReal (tw a true) • Measure.dirac true

lemma tb_single (a : ℝ) (b : Bool) : (tb a) {b} = ENNReal.ofReal (tw a b) := by
  cases b <;> simp [tb]

instance tb_prob (a : ℝ) : IsProbabilityMeasure (tb a) := by
  constructor
  have hu : (Set.univ : Set Bool) = {false} ∪ {true} := by ext b; cases b <;> simp
  rw [hu, measure_union (by simp) (measurableSet_singleton _), tb_single, tb_single,
    ← ENNReal.ofReal_add (tw_pos _ _).le (tw_pos _ _).le, tw_false, tw_true]
  ring_nf
  simp

lemma tb_real (a : ℝ) (b : Bool) : (tb a).real {b} = tw a b := by
  rw [measureReal_def, tb_single, ENNReal.toReal_ofReal (tw_pos a b).le]

lemma integral_tb (a : ℝ) (f : Bool → ℝ) :
    ∫ b, f b ∂(tb a) = f false * ((1 + tanh a) / 2) + f true * ((1 - tanh a) / 2) := by
  rw [integral_fintype (Integrable.of_finite)]
  simp [tb_real, tw_false, tw_true]
  ring

/-- product of tilted Bernoullis. -/
noncomputable def Ph {N : ℕ} (a : Fin N → ℝ) : Measure (Fin N → Bool) :=
  Measure.pi fun i => tb (a i)

instance Ph_prob {N : ℕ} (a : Fin N → ℝ) : IsProbabilityMeasure (Ph a) := by
  unfold Ph; infer_instance

lemma Ph_real_single {N : ℕ} (a : Fin N → ℝ) (e : Fin N → Bool) :
    (Ph a).real {e} = ∏ i, tw (a i) (e i) := by
  have hs : ({e} : Set (Fin N → Bool)) = Set.pi Set.univ (fun i => {e i}) := by
    ext f; simp [funext_iff]
  rw [measureReal_def, Ph, hs, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [tb_single, ENNReal.toReal_ofReal (tw_pos _ _).le]

lemma integral_Ph {N : ℕ} (a : Fin N → ℝ) (f : (Fin N → Bool) → ℝ) :
    ∫ e, f e ∂(Ph a) = ∑ e, f e * ∏ i, tw (a i) (e i) := by
  rw [integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Ph_real_single, smul_eq_mul, mul_comm]

lemma integral_eval {N : ℕ} (a : Fin N → ℝ) (i : Fin N) (f : Bool → ℝ) :
    ∫ e, f (e i) ∂(Ph a) = ∫ b, f b ∂(tb (a i)) := by
  rw [← (measurePreserving_eval (fun j => tb (a j)) i).map_eq,
    integral_map (measurable_pi_apply i).aemeasurable
      (Measurable.of_discrete (f := f)).aestronglyMeasurable]
  rfl

lemma prod_tw {N : ℕ} (h : ℝ) (d : Fin N → ℝ) (e : Fin N → Bool) :
    ∏ i, tw (h * d i) (e i) =
      exp (h * ∑ i, (if e i then (-1 : ℝ) else 1) * d i) /
        (2 ^ N * exp (∑ i, log (cosh (h * d i)))) := by
  have hc : exp (∑ i, log (cosh (h * d i))) = ∏ i, cosh (h * d i) := by
    rw [exp_sum]; exact Finset.prod_congr rfl fun i _ => exp_log (cosh_pos _)
  unfold tw
  rw [Finset.prod_div_distrib, ← exp_sum, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.mul_sum, hc]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_; unfold sg; ring

/-- Change of measure: `#{t < S}/2^N = e^{Λ - h t} E_h[g_{hσ}((S - t)/σ)]`. -/
theorem tilt_count {N : ℕ} (h σ t : ℝ) (hσ : 0 < σ) (d : Fin N → ℝ) :
    ((univ.filter (fun e : Fin N → Bool =>
        t < ∑ i, (if e i then (-1 : ℝ) else 1) * d i)).card : ℝ) / 2 ^ N =
      exp (∑ i, log (cosh (h * d i)) - h * t) *
        ∫ e, lapG (h * σ) ((∑ i, (if e i then (-1 : ℝ) else 1) * d i - t) / σ)
          ∂(Ph fun i => h * d i) := by
  rw [integral_Ph, Finset.mul_sum, Finset.card_filter, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [prod_tw]
  set S := ∑ i, (if e i then (-1 : ℝ) else 1) * d i
  set L := ∑ i, log (cosh (h * d i))
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  unfold lapG
  by_cases hS : t < S
  · have hp : 0 < (S - t) / σ := div_pos (by linarith) hσ
    rw [if_pos hS, if_pos hp]
    have e1 : h * σ * ((S - t) / σ) = h * (S - t) := by field_simp
    rw [e1, Nat.cast_one]
    have e3 : exp (L - h * t) * exp (-(h * (S - t))) * exp (h * S) = exp L := by
      rw [← exp_add, ← exp_add]; congr 1; ring
    rw [show exp (L - h * t) * (exp (-(h * (S - t))) * (exp (h * S) / (2 ^ N * exp L))) =
      (exp (L - h * t) * exp (-(h * (S - t))) * exp (h * S)) / (2 ^ N * exp L) by ring, e3]
    field_simp
  · have hp : ¬ 0 < (S - t) / σ := by
      rw [div_pos_iff_of_pos_right hσ]; linarith
    rw [if_neg hS, if_neg hp]; simp

section BE

variable {N : ℕ}

/-- Berry–Esseen on the tilted product space, from `bdd_BE`. -/
lemma be_pi (a : Fin N → ℝ) (X : Fin N → Bool → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : ∀ i b, |X i b| ≤ δ) (h0 : ∀ i, ∫ b, X i b ∂(tb (a i)) = 0)
    (h1 : ∑ i, ∫ b, X i b ^ 2 ∂(tb (a i)) = 1) (z : ℝ) :
    |((Ph a) {e | ∑ i, X i (e i) < z}).toReal - Phi z| ≤ 7 * δ := by
  have hind : iIndepFun (fun i (e : Fin N → Bool) => X i (e i)) (Ph a) :=
    iIndepFun_pi (μ := fun i => tb (a i)) (fun i => (Measurable.of_discrete (f := X i)).aemeasurable)
  refine bdd_BE (fun i (e : Fin N → Bool) => X i (e i)) hind
    (fun i => (Measurable.of_discrete (f := X i)).comp (measurable_pi_apply i)) hδ
    (fun i e => hb i (e i)) (fun i => by rw [integral_eval]; exact h0 i) ?_ hδ1 z
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_eval a i (fun b => X i b ^ 2)

lemma gauss_Iio (c : ℝ) : (gaussianReal 0 1).real (Iio c) = Phi c := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [Phi, cdf_eq_real, measureReal_def, measureReal_def, measure_congr Iio_ae_eq_Iic]

/-- Laplace functional under the tilt is within `14 δ` of the Gaussian value. -/
theorem tilt_lap (a : Fin N → ℝ) (X : Fin N → Bool → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : ∀ i b, |X i b| ≤ δ) (h0 : ∀ i, ∫ b, X i b ∂(tb (a i)) = 0)
    (h1 : ∑ i, ∫ b, X i b ^ 2 ∂(tb (a i)) = 1) {u : ℝ} (hu : 0 ≤ u) :
    |∫ e, lapG u (∑ i, X i (e i)) ∂(Ph a) - exp (u ^ 2 / 2) * (1 - Phi u)| ≤ 14 * δ := by
  set W : (Fin N → Bool) → ℝ := fun e => ∑ i, X i (e i) with hW
  have hWm : Measurable W := Measurable.of_discrete
  have : IsProbabilityMeasure ((Ph a).map W) := Measure.isProbabilityMeasure_map hWm.aemeasurable
  have hmap : ∫ e, lapG u (W e) ∂(Ph a) = ∫ w, lapG u w ∂((Ph a).map W) :=
    (integral_map hWm.aemeasurable (measurable_lapG u).aestronglyMeasurable).symm
  rw [hmap, ← lap_gauss u]
  have hlt : ∀ c, |((Ph a).map W).real (Iio c) - (gaussianReal 0 1).real (Iio c)| ≤ 7 * δ := by
    intro c
    rw [gauss_Iio, measureReal_def, Measure.map_apply hWm measurableSet_Iio]
    exact be_pi a X hδ hδ1 hb h0 h1 c
  have hle : |((Ph a).map W).real (Iic 0) - (gaussianReal 0 1).real (Iic 0)| ≤ 7 * δ := by
    have hneg := be_pi a (fun i b => -X i b) hδ hδ1 (fun i b => by rw [abs_neg]; exact hb i b)
      (fun i => by rw [integral_neg, h0, neg_zero])
      (by simpa only [neg_sq] using h1) 0
    have g0 : (gaussianReal 0 1).real (Iic 0) = Phi 0 := by rw [Phi, cdf_eq_real]
    rw [g0, measureReal_def, Measure.map_apply hWm measurableSet_Iic]
    have hc : {e : Fin N → Bool | ∑ i, -X i (e i) < 0} = (W ⁻¹' Iic 0)ᶜ := by
      ext e; simp [hW, Finset.sum_neg_distrib]
    rw [hc, prob_compl_eq_one_sub (hWm measurableSet_Iic),
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one] at hneg
    rw [Phi_zero] at hneg ⊢
    rw [abs_le] at hneg ⊢; constructor <;> linarith [hneg.1, hneg.2]
  have := lap_cmp ((Ph a).map W) (gaussianReal 0 1) hlt hle hu
  linarith [this, le_abs_self (∫ w, lapG u w ∂((Ph a).map W) - ∫ w, lapG u w ∂(gaussianReal 0 1))]

end BE

end P99bcb804

end X35_Tilt

section X36_Tanh

/-! Elementary bounds on `tanh`, `cosh`, `log ∘ cosh` used by the Esscher tilt of
Rademacher sums (KMT 1976 II, Lemma B). -/

open Real

namespace P99bcb804

lemma sinh_le_mul_cosh {a : ℝ} (ha : 0 ≤ a) : sinh a ≤ a * cosh a := by
  have hd : ∀ x, HasDerivAt (fun x => x * cosh x - sinh x) (x * sinh x) x := fun x => by
    have := ((hasDerivAt_id' x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x)
    refine this.congr_deriv ?_
    simp only [one_mul]; ring
  have hmono : Monotone (fun x => x * cosh x - sinh x) := monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    (fun x => by
      rw [(hd x).deriv]
      rcases le_total 0 x with h | h
      · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr h)
      · have : sinh x ≤ 0 := by
          have := Real.sinh_nonneg_iff.mpr (neg_nonneg.mpr h); rw [Real.sinh_neg] at this; linarith
        nlinarith)
  have := hmono ha
  simp only [Real.cosh_zero, Real.sinh_zero, zero_mul, sub_zero] at this
  linarith

lemma abs_le_abs_sinh (x : ℝ) : |x| ≤ |sinh x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
    exact Real.self_le_sinh_iff.mpr h
  · have h' := Real.self_le_sinh_iff.mpr (neg_nonneg.mpr h)
    rw [Real.sinh_neg] at h'
    rw [abs_of_nonpos h, abs_of_nonpos (by linarith)]
    linarith

lemma one_add_sq_half_le_cosh (a : ℝ) : 1 + a ^ 2 / 2 ≤ cosh a := by
  have e : cosh a = 1 + 2 * sinh (a / 2) ^ 2 := by
    have := Real.cosh_two_mul (a / 2)
    rw [show 2 * (a / 2) = a by ring, Real.cosh_sq] at this
    linarith
  have h := abs_le_abs_sinh (a / 2)
  have h2 : (a / 2) ^ 2 ≤ sinh (a / 2) ^ 2 := by
    rw [← sq_abs (a / 2), ← sq_abs (sinh (a / 2))]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [e]; nlinarith

lemma cosh_le_one_add_sq {a : ℝ} (ha : |a| ≤ 1) : cosh a ≤ 1 + a ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq a
  have hx : |a ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    have : a ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg a]
    linarith
  have h2 := Real.exp_bound hx (n := 1) one_pos
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    pow_one, Nat.succ_eq_add_one, zero_add, mul_one] at h2
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ a ^ 2 / 2)] at h2
  have := (abs_le.mp h2).2
  norm_num at this
  linarith

lemma tanh_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ tanh a := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr ha) (Real.cosh_pos a).le

lemma tanh_le_self {a : ℝ} (ha : 0 ≤ a) : tanh a ≤ a := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos a)]
  exact sinh_le_mul_cosh ha

lemma le_tanh {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : a * (1 - a ^ 2) ≤ tanh a := by
  rw [Real.tanh_eq_sinh_div_cosh, le_div_iff₀ (Real.cosh_pos a)]
  have hc := cosh_le_one_add_sq (a := a) (by rw [abs_of_nonneg ha]; exact ha1)
  have hs := Real.self_le_sinh_iff.mpr ha
  have h0 : 0 ≤ a * (1 - a ^ 2) := mul_nonneg ha (by nlinarith)
  calc a * (1 - a ^ 2) * cosh a ≤ a * (1 - a ^ 2) * (1 + a ^ 2) :=
        mul_le_mul_of_nonneg_left hc h0
    _ ≤ a := by nlinarith [pow_nonneg ha 5]
    _ ≤ sinh a := hs

/-- `a² - a⁴ ≤ a tanh a ≤ a²` for `|a| ≤ 1`. -/
lemma mul_tanh_bounds {a : ℝ} (ha : |a| ≤ 1) :
    a ^ 2 - a ^ 4 ≤ a * tanh a ∧ a * tanh a ≤ a ^ 2 := by
  have key : ∀ b : ℝ, 0 ≤ b → b ≤ 1 → b ^ 2 - b ^ 4 ≤ b * tanh b ∧ b * tanh b ≤ b ^ 2 := by
    intro b hb hb1
    have h1 := le_tanh hb hb1
    have h2 := tanh_le_self hb
    constructor
    · have := mul_le_mul_of_nonneg_left h1 hb; nlinarith
    · have := mul_le_mul_of_nonneg_left h2 hb; nlinarith
  rcases le_total 0 a with h | h
  · exact key a h (by rwa [abs_of_nonneg h] at ha)
  · have := key (-a) (by linarith) (by rw [abs_of_nonpos h] at ha; linarith)
    rw [Real.tanh_neg] at this
    constructor <;> nlinarith [this.1, this.2]

lemma tanh_sq_le (a : ℝ) : tanh a ^ 2 ≤ a ^ 2 := by
  rcases le_total 0 a with h | h
  · exact pow_le_pow_left₀ (tanh_nonneg h) (tanh_le_self h) 2
  · have h1 := tanh_nonneg (neg_nonneg.mpr h)
    have h2 := tanh_le_self (neg_nonneg.mpr h)
    rw [Real.tanh_neg] at h1 h2
    nlinarith

/-- `a²/2 - a⁴/4 ≤ log cosh a ≤ a²/2`. -/
lemma log_cosh_bounds (a : ℝ) :
    a ^ 2 / 2 - a ^ 4 / 4 ≤ log (cosh a) ∧ log (cosh a) ≤ a ^ 2 / 2 := by
  constructor
  · have hx : 0 ≤ a ^ 2 / 2 := by positivity
    have h1 := Real.one_sub_inv_le_log_of_pos (x := 1 + a ^ 2 / 2) (by linarith)
    have h2 := Real.log_le_log (by linarith) (one_add_sq_half_le_cosh a)
    have h3 : a ^ 2 / 2 - a ^ 4 / 4 ≤ 1 - (1 + a ^ 2 / 2)⁻¹ := by
      rw [show 1 - (1 + a ^ 2 / 2)⁻¹ = (a ^ 2 / 2) / (1 + a ^ 2 / 2) by field_simp; ring,
        le_div_iff₀ (by linarith)]
      nlinarith [pow_nonneg hx 3]
    linarith
  · have := Real.log_le_log (Real.cosh_pos a) (Real.cosh_le_exp_half_sq a)
    rwa [Real.log_exp] at this

lemma continuous_tanh' : Continuous tanh := by
  have : tanh = fun x => sinh x / cosh x := funext fun x => Real.tanh_eq_sinh_div_cosh x
  rw [this]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

end P99bcb804

end X36_Tanh

section X37_Cram

/-! KMT 1976 II, Lemma B (pp.42-43): assembly of the Cramér estimate for Rademacher-weighted
sums from the Esscher tilt (`tilt_count`, `tilt_lap`). -/

open MeasureTheory ProbabilityTheory Real Set Finset

namespace P99bcb804

/-- Tilted Berry–Esseen in closed form: with `a_i = h d_i`, `σ² = Σ d_i²(1 - tanh² a_i)`,
`t = Σ d_i tanh a_i`, `Λ = Σ log cosh a_i`:
`|#{t < S}/2^N - e^{Λ - h t} ψ(hσ)| ≤ e^{Λ - h t} · 14 · 2M/σ`, `ψ(u) = e^{u²/2}(1 - Φ(u))`. -/
theorem tilt_main {N : ℕ} (d : Fin N → ℝ) {h M : ℝ} (hh : 0 ≤ h) (hM0 : 0 < M)
    (hM : ∀ i, |d i| ≤ M)
    (hσ0 : 0 < ∑ i, d i ^ 2 * (1 - tanh (h * d i) ^ 2))
    (hδ1 : 2 * M ≤ √(∑ i, d i ^ 2 * (1 - tanh (h * d i) ^ 2))) :
    |((univ.filter (fun e : Fin N → Bool =>
        ∑ i, d i * tanh (h * d i) < ∑ i, (if e i then (-1 : ℝ) else 1) * d i)).card : ℝ) / 2 ^ N -
      exp (∑ i, log (cosh (h * d i)) - h * ∑ i, d i * tanh (h * d i)) *
        (exp ((h * √(∑ i, d i ^ 2 * (1 - tanh (h * d i) ^ 2))) ^ 2 / 2) *
          (1 - Phi (h * √(∑ i, d i ^ 2 * (1 - tanh (h * d i) ^ 2)))))| ≤
      exp (∑ i, log (cosh (h * d i)) - h * ∑ i, d i * tanh (h * d i)) *
        (14 * (2 * M / √(∑ i, d i ^ 2 * (1 - tanh (h * d i) ^ 2)))) := by
  set V := ∑ i, d i ^ 2 * (1 - tanh (h * d i) ^ 2) with hV
  set σ := √V with hσdef
  set t := ∑ i, d i * tanh (h * d i) with ht
  set L := ∑ i, log (cosh (h * d i)) with hL
  have hσ : 0 < σ := Real.sqrt_pos.2 hσ0
  have hσ2 : σ ^ 2 = V := Real.sq_sqrt hσ0.le
  rw [tilt_count h σ t hσ d]
  set X : Fin N → Bool → ℝ := fun i b => (sg b * d i - d i * tanh (h * d i)) / σ with hX
  have hW : ∀ e : Fin N → Bool,
      (∑ i, (if e i then (-1 : ℝ) else 1) * d i - t) / σ = ∑ i, X i (e i) := by
    intro e
    simp only [hX]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    rfl
  simp_rw [hW]
  have hδ : 0 < 2 * M / σ := by positivity
  have hδ1' : 2 * M / σ ≤ 1 := by rw [div_le_one hσ]; exact hδ1
  have hu : 0 ≤ h * σ := mul_nonneg hh hσ.le
  have hb : ∀ i b, |X i b| ≤ 2 * M / σ := by
    intro i b
    have hT := Real.abs_tanh_lt_one (h * d i)
    have hs : |sg b - tanh (h * d i)| ≤ 2 := by
      rw [abs_lt] at hT
      cases b <;> simp only [sg, ↓reduceIte, Bool.false_eq_true] <;>
        (rw [abs_le]; constructor <;> linarith [hT.1, hT.2])
    simp only [hX]
    rw [abs_div, abs_of_pos hσ, div_le_div_iff_of_pos_right hσ]
    calc |sg b * d i - d i * tanh (h * d i)| = |d i * (sg b - tanh (h * d i))| := by
          congr 1; ring
      _ = |d i| * |sg b - tanh (h * d i)| := abs_mul _ _
      _ ≤ M * 2 := mul_le_mul (hM i) hs (abs_nonneg _) hM0.le
      _ = 2 * M := by ring
  have h0 : ∀ i, ∫ b, X i b ∂(tb (h * d i)) = 0 := by
    intro i
    rw [integral_tb]
    simp only [hX, sg, ↓reduceIte, Bool.false_eq_true]
    field_simp
    ring
  have h1 : ∑ i, ∫ b, X i b ^ 2 ∂(tb (h * d i)) = 1 := by
    have e : ∀ i, ∫ b, X i b ^ 2 ∂(tb (h * d i)) = d i ^ 2 * (1 - tanh (h * d i) ^ 2) / σ ^ 2 := by
      intro i
      rw [integral_tb]
      simp only [hX, sg, ↓reduceIte, Bool.false_eq_true]
      field_simp
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.sum_div, ← hV, hσ2, div_self hσ0.ne']
  have key := tilt_lap (fun i => h * d i) X hδ hδ1' hb h0 h1 hu
  rw [← mul_sub, abs_mul, abs_of_pos (exp_pos _)]
  exact mul_le_mul_of_nonneg_left key (exp_pos _).le

/-- Choice of the tilt parameter by the intermediate value theorem. -/
lemma ivt_h {N : ℕ} (d : Fin N → ℝ) {M B2 t : ℝ} (hM0 : 0 < M) (hB : 0 < B2)
    (hB2 : ∑ i, d i ^ 2 = B2) (hM : ∀ i, |d i| ≤ M) (ht : 0 ≤ t)
    (hsmall : 2 * t / B2 * M ≤ 1 / 2) :
    ∃ h, 0 ≤ h ∧ h ≤ 2 * t / B2 ∧ ∑ i, d i * tanh (h * d i) = t := by
  rcases ht.eq_or_lt with ht0 | htp
  · exact ⟨0, le_rfl, by rw [← ht0]; simp, by rw [← ht0]; simp⟩
  set h1 := 2 * t / B2 with hh1
  have hh1p : 0 < h1 := by positivity
  have hcont : Continuous fun h : ℝ => ∑ i, d i * tanh (h * d i) :=
    continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_tanh'.comp (continuous_id.mul continuous_const))
  have hm0 : (fun h : ℝ => ∑ i, d i * tanh (h * d i)) 0 = 0 := by simp
  have hm1 : t ≤ ∑ i, d i * tanh (h1 * d i) := by
    have hterm : ∀ i, 3 / 4 * (h1 * d i) ^ 2 ≤ h1 * (d i * tanh (h1 * d i)) := by
      intro i
      have ha : |h1 * d i| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos hh1p]
        exact (mul_le_mul_of_nonneg_left (hM i) hh1p.le).trans hsmall
      have ha1 : |h1 * d i| ≤ 1 := ha.trans (by norm_num)
      have hb := (mul_tanh_bounds ha1).1
      have hsq : (h1 * d i) ^ 2 ≤ 1 / 4 := by
        have := sq_le_sq' (abs_le.1 ha).1 (abs_le.1 ha).2
        linarith
      have h4 : (h1 * d i) ^ 4 ≤ (h1 * d i) ^ 2 / 4 := by
        have e : (h1 * d i) ^ 4 = (h1 * d i) ^ 2 * (h1 * d i) ^ 2 := by ring
        rw [e]; nlinarith [sq_nonneg (h1 * d i)]
      have e2 : h1 * (d i * tanh (h1 * d i)) = h1 * d i * tanh (h1 * d i) := by ring
      rw [e2]; linarith
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
    have e3 : ∑ i, (h1 * d i) ^ 2 = h1 ^ 2 * B2 := by
      rw [← hB2, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e3] at hs
    have e4 : 3 / 4 * (h1 ^ 2 * B2) = h1 * (3 / 2 * t) := by
      rw [hh1]; field_simp; ring
    rw [e4] at hs
    have := le_of_mul_le_mul_left hs hh1p
    linarith
  obtain ⟨h, hmem, hval⟩ := intermediate_value_Icc hh1p.le hcont.continuousOn
    ⟨by simp [ht], hm1⟩
  exact ⟨h, hmem.1, hmem.2, hval⟩

end P99bcb804

end X37_Cram

section X38_Cram2

/-! KMT 1976 II, Lemma B: the elementary estimates of the tilt parameter, cumulant and
variance, and the final two-sided combination. -/

open Real Finset

namespace P99bcb804

lemma term_tanh {h d : ℝ} (hh : 0 ≤ h) (ha : |h * d| ≤ 1) :
    h * d ^ 2 - h ^ 3 * d ^ 4 ≤ d * tanh (h * d) ∧ d * tanh (h * d) ≤ h * d ^ 2 := by
  rcases hh.eq_or_lt with h0 | hp
  · subst h0; simp
  · obtain ⟨h1, h2⟩ := mul_tanh_bounds ha
    have e1 : h * (h * d ^ 2 - h ^ 3 * d ^ 4) = (h * d) ^ 2 - (h * d) ^ 4 := by ring
    have e2 : h * (d * tanh (h * d)) = h * d * tanh (h * d) := by ring
    have e3 : h * (h * d ^ 2) = (h * d) ^ 2 := by ring
    exact ⟨le_of_mul_le_mul_left (by rw [e1, e2]; exact h1) hp,
      le_of_mul_le_mul_left (by rw [e3, e2]; exact h2) hp⟩

variable {N : ℕ}

lemma t_bounds (d : Fin N → ℝ) {h : ℝ} (hh : 0 ≤ h) (ha : ∀ i, |h * d i| ≤ 1) :
    h * ∑ i, d i ^ 2 - h ^ 3 * ∑ i, d i ^ 4 ≤ ∑ i, d i * tanh (h * d i) ∧
      ∑ i, d i * tanh (h * d i) ≤ h * ∑ i, d i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact ⟨Finset.sum_le_sum fun i _ => (term_tanh hh (ha i)).1,
    Finset.sum_le_sum fun i _ => (term_tanh hh (ha i)).2⟩

lemma lam_bounds (d : Fin N → ℝ) (h : ℝ) :
    h ^ 2 * (∑ i, d i ^ 2) / 2 - h ^ 4 * (∑ i, d i ^ 4) / 4 ≤ ∑ i, log (cosh (h * d i)) ∧
      ∑ i, log (cosh (h * d i)) ≤ h ^ 2 * (∑ i, d i ^ 2) / 2 := by
  have e1 : h ^ 2 * (∑ i, d i ^ 2) / 2 - h ^ 4 * (∑ i, d i ^ 4) / 4 =
      ∑ i, ((h * d i) ^ 2 / 2 - (h * d i) ^ 4 / 4) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
    congr 2 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : h ^ 2 * (∑ i, d i ^ 2) / 2 = ∑ i, (h * d i) ^ 2 / 2 := by
    rw [← Finset.sum_div, Finset.mul_sum]
    congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  constructor
  · rw [e1]; exact Finset.sum_le_sum fun i _ => (log_cosh_bounds _).1
  · rw [e2]; exact Finset.sum_le_sum fun i _ => (log_cosh_bounds _).2

lemma V_bounds (d : Fin N → ℝ) (h : ℝ) :
    ∑ i, d i ^ 2 - h ^ 2 * ∑ i, d i ^ 4 ≤ ∑ i, d i ^ 2 * (1 - tanh (h * d i) ^ 2) ∧
      ∑ i, d i ^ 2 * (1 - tanh (h * d i) ^ 2) ≤ ∑ i, d i ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  constructor
  · refine Finset.sum_le_sum fun i _ => ?_
    have := tanh_sq_le (h * d i)
    have hd : 0 ≤ d i ^ 2 := sq_nonneg _
    have e : d i ^ 2 - h ^ 2 * d i ^ 4 = d i ^ 2 * (1 - (h * d i) ^ 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hd
  · refine Finset.sum_le_sum fun i _ => ?_
    have := sq_nonneg (tanh (h * d i))
    have hd : 0 ≤ d i ^ 2 := sq_nonneg _
    nlinarith

lemma Q_le (d : Fin N → ℝ) {M : ℝ} (hM : ∀ i, |d i| ≤ M) :
    ∑ i, d i ^ 4 ≤ M ^ 2 * ∑ i, d i ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : d i ^ 2 ≤ M ^ 2 := by
    have := hM i
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  have e : d i ^ 4 = d i ^ 2 * d i ^ 2 := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

lemma B2_le (d : Fin N → ℝ) {M : ℝ} (hM : ∀ i, |d i| ≤ M) :
    ∑ i, d i ^ 2 ≤ M ^ 2 * N := by
  calc ∑ i, d i ^ 2 ≤ ∑ _i : Fin N, M ^ 2 := Finset.sum_le_sum fun i _ => by
        have := hM i
        exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
    _ = M ^ 2 * N := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma E1_bound {B2 h t L Q : ℝ} (hB : 0 < B2) (hh : 0 ≤ h) (hQ : 0 ≤ Q)
    (ht1 : h * B2 - h ^ 3 * Q ≤ t) (ht2 : t ≤ h * B2)
    (hL1 : h ^ 2 * B2 / 2 - h ^ 4 * Q / 4 ≤ L) (hL2 : L ≤ h ^ 2 * B2 / 2) :
    |L - h * t + t ^ 2 / (2 * B2)| ≤ h ^ 4 * Q / 4 + (h ^ 3 * Q) ^ 2 / (2 * B2) := by
  have hid : L - h * t + t ^ 2 / (2 * B2) = (L - h ^ 2 * B2 / 2) + (h * B2 - t) ^ 2 / (2 * B2) := by
    field_simp; ring
  have hsq : (h * B2 - t) ^ 2 ≤ (h ^ 3 * Q) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hdiv : (h * B2 - t) ^ 2 / (2 * B2) ≤ (h ^ 3 * Q) ^ 2 / (2 * B2) :=
    div_le_div_of_nonneg_right hsq (by positivity)
  have hnn : 0 ≤ (h * B2 - t) ^ 2 / (2 * B2) := by positivity
  have hX : 0 ≤ (h ^ 3 * Q) ^ 2 / (2 * B2) := by positivity
  have hY : 0 ≤ h ^ 4 * Q := by positivity
  rw [hid, abs_le]; constructor <;> linarith

lemma ux_bound {B2 V h t Q : ℝ} (hB : 0 < B2) (hV : 0 < V) (hh : 0 ≤ h) (hQ : 0 ≤ Q)
    (ht0 : 0 ≤ t) (ht1 : h * B2 - h ^ 3 * Q ≤ t) (ht2 : t ≤ h * B2)
    (hV1 : B2 - h ^ 2 * Q ≤ V) (hV2 : V ≤ B2) :
    0 ≤ h * √V ∧ h * √V ≤ h * √B2 ∧ 0 ≤ t / √B2 ∧ t / √B2 ≤ h * √B2 ∧
      |h * √V - t / √B2| ≤ h ^ 3 * Q / √B2 := by
  have hs : 0 < √B2 := Real.sqrt_pos.2 hB
  have hu0 : 0 ≤ h * √V := mul_nonneg hh (Real.sqrt_nonneg _)
  have huD : h * √V ≤ h * √B2 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hV2) hh
  have hx0 : 0 ≤ t / √B2 := div_nonneg ht0 hs.le
  have eD : h * B2 / √B2 = h * √B2 := by
    rw [mul_div_assoc, Real.div_sqrt]
  have hxD : t / √B2 ≤ h * √B2 := by
    rw [← eD]; exact div_le_div_of_nonneg_right ht2 hs.le
  have hxL : h * √B2 - h ^ 3 * Q / √B2 ≤ t / √B2 := by
    rw [← eD, ← sub_div]; exact div_le_div_of_nonneg_right ht1 hs.le
  have huL : h * √B2 - h ^ 3 * Q / √B2 ≤ h * √V := by
    rcases hh.eq_or_lt with h0 | hp
    · subst h0; simp
    · set D := h * √B2 with hDdef
      set u := h * √V with hudef
      have hD : 0 < D := mul_pos hp hs
      have hu2 : u ^ 2 = h ^ 2 * V := by rw [hudef, mul_pow, Real.sq_sqrt hV.le]
      have hD2 : D ^ 2 = h ^ 2 * B2 := by rw [hDdef, mul_pow, Real.sq_sqrt hB.le]
      have hdiff : D ^ 2 - u ^ 2 ≤ h ^ 4 * Q := by
        rw [hu2, hD2]
        have := mul_le_mul_of_nonneg_left hV1 (sq_nonneg h)
        nlinarith
      have e : h ^ 3 * Q / √B2 * D = h ^ 4 * Q := by
        rw [hDdef]; field_simp
      have hk : (D - u) * D ≤ h ^ 3 * Q / √B2 * D := by
        rw [e]
        have : (D - u) * D ≤ (D - u) * (D + u) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        nlinarith
      have := le_of_mul_le_mul_right hk hD
      linarith
  refine ⟨hu0, huD, hx0, hxD, ?_⟩
  rw [abs_le]; constructor <;> linarith

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

section X41_Dperm

/-! KMT 1976 II, (4.7) instantiated for pairings `w : Perm (Fin N ⊕ Fin N)`:
the pair variance `sw2 x w = σ_w²/N` and the averaged Gaussian tail. Iteration file: imports the
helper modules `P99bcb804Mills/Delta/L4` (oleans built by scratch/probe/99bcb804_mods/build.sh). -/

open Finset Real

namespace P99bcb804

/-! Constants. -/

/-! Named quantities: `s = sS x`, `α = kα x y`, `L = kL c y N`, `Y = kY y N`. -/
noncomputable def kY (y : ℝ) (N : ℕ) : ℝ := (y ^ 3 + 1) / √(N : ℝ)

end P99bcb804

end X41_Dperm

section X42_Cram3

/-! KMT 1976 II, Lemma B (pp.42-43): Cramér estimate for Rademacher-weighted sums. -/

open Real Finset

namespace P99bcb804

/-- copy of the statement in `99bcb804_fpc.lean`. -/
def SignCramer : Prop :=
  ∀ M b : ℝ, 0 < M → 0 < b → ∃ ε C N0 : ℝ, 0 < ε ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N → N0 ≤ N →
    ∀ d : Fin N → ℝ, (∀ i, |d i| ≤ M) → b * N ≤ ∑ i, d i ^ 2 →
    ∀ y : ℝ, 0 ≤ y → y ≤ ε * √(N : ℝ) →
      (1 - Phi (y * √(N : ℝ) / √(∑ i, d i ^ 2))) * exp (-(C * kY y N)) ≤
        ((univ.filter (fun e : Fin N → Bool =>
          y * √(N : ℝ) < ∑ i, (if e i then (-1 : ℝ) else 1) * d i)).card : ℝ) / 2 ^ N ∧
      ((univ.filter (fun e : Fin N → Bool =>
          y * √(N : ℝ) < ∑ i, (if e i then (-1 : ℝ) else 1) * d i)).card : ℝ) / 2 ^ N ≤
        (1 - Phi (y * √(N : ℝ) / √(∑ i, d i ^ 2))) * exp (C * kY y N)

/-- The polynomial error terms, all `O(h³ N) = O(y³/√N)`. -/
lemma quant {M b sn h y B2 Q : ℝ} (hM : 0 < M) (hb : 0 < b) (hsn1 : 1 ≤ sn) (hh : 0 ≤ h)
    (hh1 : h ≤ 1) (hw : h * sn ≤ 2 * y / b) (hB : 0 < B2) (hBn : B2 ≤ M ^ 2 * sn ^ 2)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ M ^ 2 * B2) :
    h ^ 4 * Q / 4 + (h ^ 3 * Q) ^ 2 / (2 * B2) + 17 * (h ^ 3 * Q / √B2) * (h * √B2) +
        h ^ 3 * Q / √B2 + 8 * (h ^ 3 * Q / √B2) ^ 2 ≤
      (M ^ 4 / 4 + M ^ 6 / 2 + 17 * M ^ 4 + M ^ 3 + 8 * M ^ 6) * (8 * y ^ 3 / b ^ 3) / sn := by
  have hsn0 : 0 < sn := by linarith
  have hs0 : 0 < √B2 := Real.sqrt_pos.2 hB
  have hs : √B2 ≤ M * sn := by
    rw [Real.sqrt_le_left (by positivity)]; rw [mul_pow]; exact hBn
  have hsB : √B2 * √B2 = B2 := Real.mul_self_sqrt hB.le
  have hQs : Q / √B2 ≤ M ^ 2 * (M * sn) := by
    rw [div_le_iff₀ hs0]
    calc Q ≤ M ^ 2 * B2 := hQ
      _ = M ^ 2 * √B2 * √B2 := by rw [mul_assoc, hsB]
      _ ≤ M ^ 2 * (M * sn) * √B2 := by gcongr
  set U := h ^ 3 * sn ^ 2 with hU
  have hU0 : 0 ≤ U := by positivity
  have hη : h ^ 3 * Q / √B2 ≤ h ^ 3 * M ^ 3 * sn := by
    rw [mul_div_assoc]
    calc h ^ 3 * (Q / √B2) ≤ h ^ 3 * (M ^ 2 * (M * sn)) := by gcongr
      _ = h ^ 3 * M ^ 3 * sn := by ring
  have hη0 : 0 ≤ h ^ 3 * Q / √B2 := by positivity
  have hh4 : h ^ 4 ≤ h ^ 3 := by
    calc h ^ 4 = h ^ 3 * h := by ring
      _ ≤ h ^ 3 * 1 := by gcongr
      _ = h ^ 3 := by ring
  have hh6 : h ^ 6 ≤ h ^ 3 := by
    calc h ^ 6 = h ^ 3 * h ^ 3 := by ring
      _ ≤ h ^ 3 * 1 := by gcongr; exact pow_le_one₀ hh hh1
      _ = h ^ 3 := by ring
  have t1 : h ^ 4 * Q / 4 ≤ M ^ 4 / 4 * U := by
    calc h ^ 4 * Q / 4 ≤ h ^ 4 * (M ^ 2 * (M ^ 2 * sn ^ 2)) / 4 := by
          gcongr; exact hQ.trans (by gcongr)
      _ ≤ h ^ 3 * (M ^ 2 * (M ^ 2 * sn ^ 2)) / 4 := by gcongr
      _ = M ^ 4 / 4 * U := by rw [hU]; ring
  have t2 : (h ^ 3 * Q) ^ 2 / (2 * B2) ≤ M ^ 6 / 2 * U := by
    rw [div_le_iff₀ (by positivity)]
    calc (h ^ 3 * Q) ^ 2 ≤ (h ^ 3 * (M ^ 2 * B2)) ^ 2 := by gcongr
      _ = h ^ 6 * M ^ 4 * B2 * B2 := by ring
      _ ≤ h ^ 6 * M ^ 4 * (M ^ 2 * sn ^ 2) * B2 := by gcongr
      _ ≤ h ^ 3 * M ^ 4 * (M ^ 2 * sn ^ 2) * B2 := by gcongr
      _ = M ^ 6 / 2 * U * (2 * B2) := by rw [hU]; ring
  have t3 : 17 * (h ^ 3 * Q / √B2) * (h * √B2) ≤ 17 * M ^ 4 * U := by
    calc 17 * (h ^ 3 * Q / √B2) * (h * √B2) ≤ 17 * (h ^ 3 * M ^ 3 * sn) * (h * (M * sn)) := by
          gcongr
      _ = 17 * M ^ 4 * (h ^ 4 * sn ^ 2) := by ring
      _ ≤ 17 * M ^ 4 * (h ^ 3 * sn ^ 2) := by gcongr
      _ = 17 * M ^ 4 * U := by rw [hU]
  have t4 : h ^ 3 * Q / √B2 ≤ M ^ 3 * U := by
    calc h ^ 3 * Q / √B2 ≤ h ^ 3 * M ^ 3 * sn := hη
      _ = h ^ 3 * M ^ 3 * sn * 1 := by ring
      _ ≤ h ^ 3 * M ^ 3 * sn * sn := by gcongr
      _ = M ^ 3 * U := by rw [hU]; ring
  have t5 : 8 * (h ^ 3 * Q / √B2) ^ 2 ≤ 8 * M ^ 6 * U := by
    calc 8 * (h ^ 3 * Q / √B2) ^ 2 ≤ 8 * (h ^ 3 * M ^ 3 * sn) ^ 2 := by gcongr
      _ = 8 * M ^ 6 * (h ^ 6 * sn ^ 2) := by ring
      _ ≤ 8 * M ^ 6 * (h ^ 3 * sn ^ 2) := by gcongr
      _ = 8 * M ^ 6 * U := by rw [hU]
  have hUy : U ≤ 8 * y ^ 3 / b ^ 3 / sn := by
    rw [le_div_iff₀ hsn0]
    have hw0 : 0 ≤ h * sn := by positivity
    calc U * sn = (h * sn) ^ 3 := by rw [hU]; ring
      _ ≤ (2 * y / b) ^ 3 := by gcongr
      _ = 8 * y ^ 3 / b ^ 3 := by ring
  have hK : 0 ≤ M ^ 4 / 4 + M ^ 6 / 2 + 17 * M ^ 4 + M ^ 3 + 8 * M ^ 6 := by positivity
  calc _ ≤ M ^ 4 / 4 * U + M ^ 6 / 2 * U + 17 * M ^ 4 * U + M ^ 3 * U + 8 * M ^ 6 * U := by
        linarith
    _ = (M ^ 4 / 4 + M ^ 6 / 2 + 17 * M ^ 4 + M ^ 3 + 8 * M ^ 6) * U := by ring
    _ ≤ (M ^ 4 / 4 + M ^ 6 / 2 + 17 * M ^ 4 + M ^ 3 + 8 * M ^ 6) * (8 * y ^ 3 / b ^ 3 / sn) := by
        gcongr
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- KMT 1976 II, Lemma B. -/
theorem signCramer_holds : SignCramer := by
  intro M b hM hb
  set Kr : ℝ := 56 * M * √(2 * π) / √b with hKr
  have hKr0 : 0 < Kr := by positivity
  set K1 : ℝ := M ^ 4 / 4 + M ^ 6 / 2 + 17 * M ^ 4 + M ^ 3 + 8 * M ^ 6 with hK1
  have hK10 : 0 ≤ K1 := by positivity
  refine ⟨min (min (b / 2) (b / (4 * M))) (b / (128 * M * Kr)),
    8 * K1 / b ^ 3 + 2 * Kr + 64 * Kr * M / b + 1, max (16 * Kr ^ 2) (16 * M ^ 2 / b),
    by positivity, by positivity, ?_⟩
  intro N hN hN0 d hdM hbB y hy hyε
  set ε := min (min (b / 2) (b / (4 * M))) (b / (128 * M * Kr)) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ b / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ b / (4 * M) := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ b / (128 * M * Kr) := min_le_right _ _
  set n : ℝ := (N : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hN
  set sn := √n with hsn
  have hsn1 : 1 ≤ sn := Real.one_le_sqrt.2 hn1
  have hsn0 : 0 < sn := by linarith
  have hsn2 : sn ^ 2 = n := Real.sq_sqrt (by linarith)
  set B2 := ∑ i, d i ^ 2 with hB2
  set Q := ∑ i, d i ^ 4 with hQ
  have hB0 : 0 < B2 := lt_of_lt_of_le (by positivity) hbB
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => by positivity
  set t := y * sn with ht
  have ht0 : 0 ≤ t := by positivity
  have hh1b : 2 * t / B2 ≤ 2 * y / (b * sn) := by
    rw [div_le_div_iff₀ hB0 (by positivity)]
    have e : 2 * t * (b * sn) = 2 * y * (b * n) := by rw [ht, ← hsn2]; ring
    rw [e]; exact mul_le_mul_of_nonneg_left hbB (by positivity)
  have hyb : 2 * y / (b * sn) ≤ 2 * ε / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    calc 2 * y * b ≤ 2 * (ε * sn) * b := by gcongr
      _ = 2 * ε * (b * sn) := by ring
  have hsmall : 2 * t / B2 * M ≤ 1 / 2 := by
    calc 2 * t / B2 * M ≤ 2 * ε / b * M := mul_le_mul_of_nonneg_right (hh1b.trans hyb) hM.le
      _ ≤ 2 * (b / (4 * M)) / b * M := by gcongr
      _ = 1 / 2 := by field_simp; ring
  obtain ⟨h, hh0, hhle, hm⟩ := ivt_h d hM hB0 rfl hdM ht0 hsmall
  have hhw : h * sn ≤ 2 * y / b := by
    calc h * sn ≤ 2 * y / (b * sn) * sn := by gcongr; exact hhle.trans hh1b
      _ = 2 * y / b := by field_simp
  have hh1 : h ≤ 1 := by
    calc h ≤ 2 * ε / b := (hhle.trans hh1b).trans hyb
      _ ≤ 2 * (b / 2) / b := by gcongr
      _ = 1 := by field_simp
  have hhM : h * M ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hhle hM.le).trans hsmall
  have ha : ∀ i, |h * d i| ≤ 1 := fun i => by
    rw [abs_mul, abs_of_nonneg hh0]
    exact ((mul_le_mul_of_nonneg_left (hdM i) hh0).trans hhM).trans (by norm_num)
  have ht12 : h * B2 - h ^ 3 * Q ≤ t ∧ t ≤ h * B2 := by
    have := t_bounds d hh0 ha; rw [hm] at this; exact this
  obtain ⟨ht1, ht2⟩ := ht12
  set L := ∑ i, log (cosh (h * d i)) with hL
  have hL12 : h ^ 2 * B2 / 2 - h ^ 4 * Q / 4 ≤ L ∧ L ≤ h ^ 2 * B2 / 2 := lam_bounds d h
  obtain ⟨hL1, hL2⟩ := hL12
  set V := ∑ i, d i ^ 2 * (1 - tanh (h * d i) ^ 2) with hV
  have hV12 : B2 - h ^ 2 * Q ≤ V ∧ V ≤ B2 := V_bounds d h
  obtain ⟨hV1, hV2⟩ := hV12
  have hQM : Q ≤ M ^ 2 * B2 := Q_le d hdM
  have hBn : B2 ≤ M ^ 2 * sn ^ 2 := by rw [hsn2]; exact B2_le d hdM
  have hV34 : 3 / 4 * B2 ≤ V := by
    have e1 : h ^ 2 * Q ≤ (h * M) ^ 2 * B2 := by
      rw [mul_pow, mul_assoc]; exact mul_le_mul_of_nonneg_left hQM (sq_nonneg h)
    have e2 : (h * M) ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (mul_nonneg hh0 hM.le) hhM 2
    have e3 : (h * M) ^ 2 * B2 ≤ (1 / 2) ^ 2 * B2 := mul_le_mul_of_nonneg_right e2 hB0.le
    norm_num at e3
    linarith
  have hV0 : 0 < V := by linarith
  set σ := √V with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hV0
  have hσlow : √b * sn / 2 ≤ σ := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, mul_pow, Real.sq_sqrt hb.le, hsn2]; linarith
  have hδ1 : 2 * M ≤ σ := by
    have hN16 : 16 * M ^ 2 / b ≤ n := (le_max_right _ _).trans hN0
    have h16 : (4 * M) ^ 2 ≤ b * n := by
      rw [div_le_iff₀ hb] at hN16; linarith only [hN16]
    have : 4 * M ≤ √b * sn := by
      rw [hsn, ← Real.sqrt_mul hb.le]; exact Real.le_sqrt_of_sq_le h16
    linarith
  have key := tilt_main d hh0 hM hdM hV0 hδ1
  rw [hm] at key
  have hUX := ux_bound hB0 hV0 hh0 hQ0 ht0 ht1 ht2 hV1 hV2
  have hE1 := E1_bound hB0 hh0 hQ0 ht1 ht2 hL1 hL2
  set u := h * σ with hu
  set x := t / √B2 with hx
  obtain ⟨hu0, huD, hx0, hxD, hη⟩ := hUX
  set ψu := exp (u ^ 2 / 2) * (1 - Phi u) with hψu
  have hψ : 0 < ψu := mul_pos (exp_pos _) (one_sub_Phi_pos u)
  set r := 14 * (2 * M / σ) / ψu with hr
  have hrψ : r * ψu = 14 * (2 * M / σ) := div_mul_cancel₀ _ hψ.ne'
  have hr0 : 0 ≤ r := by positivity
  have hr_eq : r = 28 * M * √(2 * π) * Hz u / σ := by
    rw [hr, hψu, psi_eq]; field_simp; ring
  have hsB : √B2 ≤ M * sn := by
    rw [Real.sqrt_le_left (by positivity)]; rw [mul_pow]; exact hBn
  have hDw : h * √B2 ≤ M * (2 * y / b) := by
    calc h * √B2 ≤ h * (M * sn) := by gcongr
      _ = M * (h * sn) := by ring
      _ ≤ M * (2 * y / b) := by gcongr
  have hrK : r ≤ Kr * (1 + 32 * M * y / b) / sn := by
    have hHz : Hz u ≤ 1 + 32 * M * y / b := by
      have := Hz_le_lin hu0
      have : 16 * u ≤ 32 * M * y / b := by
        have := huD.trans hDw
        calc 16 * u ≤ 16 * (M * (2 * y / b)) := by linarith
          _ = 32 * M * y / b := by ring
      linarith
    calc r = 28 * M * √(2 * π) * Hz u / σ := hr_eq
      _ ≤ 28 * M * √(2 * π) * (1 + 32 * M * y / b) / (√b * sn / 2) := by
          gcongr
      _ = Kr * (1 + 32 * M * y / b) / sn := by rw [hKr]; field_simp; ring
  have hr1 : r ≤ 1 / 2 := by
    refine hrK.trans ?_
    rw [div_le_iff₀ hsn0]
    have hK16 : 16 * Kr ^ 2 ≤ n := (le_max_left _ _).trans hN0
    have hKs : 4 * Kr ≤ sn := by
      rw [hsn]; exact Real.le_sqrt_of_sq_le (by linarith only [hK16])
    have hy2 : 32 * Kr * M * y / b ≤ sn / 4 := by
      rw [div_le_iff₀ hb]
      calc 32 * Kr * M * y ≤ 32 * Kr * M * (ε * sn) := by gcongr
        _ ≤ 32 * Kr * M * (b / (128 * M * Kr) * sn) := by gcongr
        _ = sn / 4 * b := by field_simp; ring
    have e : Kr * (1 + 32 * M * y / b) = Kr + 32 * Kr * M * y / b := by ring
    rw [e]; linarith
  have hP : |((univ.filter (fun e : Fin N → Bool =>
        t < ∑ i, (if e i then (-1 : ℝ) else 1) * d i)).card : ℝ) / 2 ^ N - exp (L - h * t) * ψu| ≤
      exp (L - h * t) * (r * ψu) := by rw [hrψ]; exact key
  have hRB := ratio_bounds hx0 hu0
  have hlo : (1 - Phi x) * exp (x ^ 2 / 2) *
      exp ((u ^ 2 - x ^ 2) / 2 - Hz x * (u - x) - 8 * (u - x) ^ 2) ≤ ψu := by
    rw [mul_comm (1 - Phi x)]; exact hRB.1
  have hhi : ψu ≤ (1 - Phi x) * exp (x ^ 2 / 2) * exp ((u ^ 2 - x ^ 2) / 2 - Hz x * (u - x)) := by
    rw [mul_comm (1 - Phi x)]; exact hRB.2
  have hx2 : x ^ 2 / 2 = t ^ 2 / (2 * B2) := by
    rw [hx, div_pow, Real.sq_sqrt hB0.le]; ring
  have hq := quant hM hb hsn1 hh0 hh1 hhw hB0 hBn hQ0 hQM
  rw [← hK1] at hq
  set η := h ^ 3 * Q / √B2 with hηdef
  set D := h * √B2 with hD
  have hη0 : 0 ≤ η := div_nonneg (mul_nonneg (pow_nonneg hh0 3) hQ0) (Real.sqrt_nonneg _)
  have hsq : |(u ^ 2 - x ^ 2) / 2| ≤ η * D := by
    rw [show (u ^ 2 - x ^ 2) / 2 = (u - x) * ((u + x) / 2) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (u + x) / 2)]
    exact mul_le_mul hη (by linarith) (by positivity) hη0
  have hHzx : |Hz x * (u - x)| ≤ (1 + 16 * D) * η := by
    rw [abs_mul, abs_of_pos (Hz_pos x)]
    exact mul_le_mul ((Hz_le_lin hx0).trans (by linarith)) hη (abs_nonneg _) (by positivity)
  have hsq2 : (u - x) ^ 2 ≤ η ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hη 2
  have hy3 : y ≤ y ^ 3 + 1 := by
    nlinarith only [sq_nonneg (y - 1), mul_nonneg hy (sq_nonneg (y - 1)), sq_nonneg y]
  have hnum : K1 * (8 * y ^ 3 / b ^ 3) + 2 * (Kr * (1 + 32 * M * y / b)) ≤
      (8 * K1 / b ^ 3 + 2 * Kr + 64 * Kr * M / b + 1) * (y ^ 3 + 1) := by
    have h64 : 64 * Kr * M * y / b ≤ 64 * Kr * M * (y ^ 3 + 1) / b := by gcongr
    have hy30 : 0 ≤ y ^ 3 := by positivity
    have hA : 0 ≤ 8 * K1 / b ^ 3 := by positivity
    have hKy : 0 ≤ Kr * y ^ 3 := mul_nonneg hKr0.le hy30
    have e1 : K1 * (8 * y ^ 3 / b ^ 3) = 8 * K1 / b ^ 3 * y ^ 3 := by ring
    have e2 : 2 * (Kr * (1 + 32 * M * y / b)) = 2 * Kr + 64 * Kr * M * y / b := by ring
    have e3 : (8 * K1 / b ^ 3 + 2 * Kr + 64 * Kr * M / b + 1) * (y ^ 3 + 1) =
        8 * K1 / b ^ 3 * y ^ 3 + 8 * K1 / b ^ 3 + 2 * (Kr * y ^ 3) + 2 * Kr +
          64 * Kr * M * (y ^ 3 + 1) / b + (y ^ 3 + 1) := by ring
    rw [e1, e2, e3]
    linarith only [h64, hA, hKy, hy30]
  have hfin : K1 * (8 * y ^ 3 / b ^ 3) / sn + 2 * (Kr * (1 + 32 * M * y / b) / sn) ≤
      (8 * K1 / b ^ 3 + 2 * Kr + 64 * Kr * M / b + 1) * kY y N := by
    have e : K1 * (8 * y ^ 3 / b ^ 3) / sn + 2 * (Kr * (1 + 32 * M * y / b) / sn) =
        (K1 * (8 * y ^ 3 / b ^ 3) + 2 * (Kr * (1 + 32 * M * y / b))) / sn := by ring
    have e' : (8 * K1 / b ^ 3 + 2 * Kr + 64 * Kr * M / b + 1) * kY y N =
        (8 * K1 / b ^ 3 + 2 * Kr + 64 * Kr * M / b + 1) * (y ^ 3 + 1) / sn := by
      unfold kY; rw [← hn, ← hsn]; ring
    rw [e, e']
    exact div_le_div_of_nonneg_right hnum hsn0.le
  obtain ⟨hE1a, hE1b⟩ := abs_le.1 hE1
  obtain ⟨hsqa, hsqb⟩ := abs_le.1 hsq
  obtain ⟨hHa, hHb⟩ := abs_le.1 hHzx
  have hr2 : 2 * r ≤ 2 * (Kr * (1 + 32 * M * y / b) / sn) := by linarith only [hrK]
  exact combine hψ (one_sub_Phi_pos x) hP hr0 hr1 hlo hhi
    (by linarith only [hx2, hE1a, hsqa, hHb, hsq2, hq, hfin, hr2, hη0])
    (by linarith only [hx2, hE1b, hsqb, hHa, hq, hfin, hrK, hη0, hr0, hsq2, sq_nonneg η,
      sq_nonneg (u - x)])
end P99bcb804

end X42_Cram3

end P99Hyps

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ (M b : ℝ),
      (0 : ℝ) < M →
        (0 : ℝ) < b →
          ∃ (ε : ℝ) (C : ℝ) (N0 : ℝ),
            (0 : ℝ) < ε ∧
              (0 : ℝ) < C ∧
                ∀ (N : ℕ),
                  (1 : ℕ) ≤ N →
                    N0 ≤ ↑N →
                      ∀ (d : Fin N → ℝ),
                        (∀ (i : Fin N), |d i| ≤ M) →
                          b * ↑N ≤ ∑ i : Fin N, d i ^ (2 : ℕ) →
                            ∀ (y : ℝ),
                              (0 : ℝ) ≤ y →
                                y ≤ ε * √↑N →
                                  ((1 : ℝ) -
                                          (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                            (y * √↑N / √(∑ i : Fin N, d i ^ (2 : ℕ)))) *
                                        Real.exp (-(C * ((y ^ (3 : ℕ) + (1 : ℝ)) / √↑N))) ≤
                                      ↑(Finset.card
                                            {e : Fin N → Bool |
                                              y * √↑N <
                                                ∑ i : Fin N, (if e i = Bool.true then (-1 : ℝ) else (1 : ℝ)) * d i}) /
                                        (2 : ℝ) ^ N ∧
                                    ↑(Finset.card
                                            {e : Fin N → Bool |
                                              y * √↑N <
                                                ∑ i : Fin N, (if e i = Bool.true then (-1 : ℝ) else (1 : ℝ)) * d i}) /
                                        (2 : ℝ) ^ N ≤
                                      ((1 : ℝ) -
                                          (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                            (y * √↑N / √(∑ i : Fin N, d i ^ (2 : ℕ)))) *
                                        Real.exp (C * ((y ^ (3 : ℕ) + (1 : ℝ)) / √↑N)) := by
  first
  | exact P99bcb804.signCramer_holds
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.signCramer_holds <;> assumption)
