-- Prove2me | solution 1 for EthierKurtz.kmt_finite_population_cramer_average
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T01:33:46.349081+00:00
-- url     : https://prove2.me/submissions/840382cb-8990-4c49-b5d1-6182f0381020

import Mathlib
import Theorems.Thm_EthierKurtz_kmt_permutation_bilinear_mgf
import Theorems.Thm_EthierKurtz_gaussian_tail_variance_perturbation

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
  linarith [mul_le_mul_of_nonneg_left hle hx2.le]

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

lemma phi_le_phi_zero (w : ℝ) : phi w ≤ phi 0 := by
  unfold phi
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  linarith [sq_nonneg w]

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
      linarith
    have s2 : A * (p * (p - w * G)) ≤ p ^ 2 := by nlinarith
    have s3 : (w * p) ^ 2 ≤ (A * G) ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
    have s4 : w ^ 2 * (A * (p * (p - w * G))) ≤ A ^ 2 * G ^ 2 := by
      have := mul_le_mul_of_nonneg_left s2 (sq_nonneg w)
      linarith
    have s5 : w ^ 2 * (p * (p - w * G)) ≤ A * G ^ 2 := by
      have h' : A * (w ^ 2 * (p * (p - w * G))) ≤ A * (A * G ^ 2) := by linarith
      exact le_of_mul_le_mul_left h' hA0
    have hw2 : 1 ≤ w ^ 2 := by nlinarith
    have s6 : A * G ^ 2 ≤ 2 * w ^ 2 * G ^ 2 := by
      have : A ≤ 2 * w ^ 2 := by rw [hA]; linarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg G)
    have s7 : p * (p - w * G) ≤ 2 * G ^ 2 := by
      have h' : w ^ 2 * (p * (p - w * G)) ≤ w ^ 2 * (2 * G ^ 2) := by linarith
      exact le_of_mul_le_mul_left h' (by linarith)
    linarith [sq_nonneg G]
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

/-- Linearised Gaussian tail ratio (the analytic core of KMT 1976 II, (4.6)): with `d = s'² - s²`,
`β = Hz(x/s) x / (2 s³)` and `B = 1/m⁵ + 10/m⁶`, for `s, s' ≥ m > 0` and `x ≥ 0`,
`(1-Φ(x/s')) / (1-Φ(x/s)) ∈ [e^{βd - B(x²+1)d²}, e^{βd + B(x²+1)d²}]`. -/
theorem tail_ratio_lin {m s sp x : ℝ} (hm : 0 < m) (hs : m ≤ s) (hsp : m ≤ sp) (hx : 0 ≤ x) :
    1 - Phi (x / sp) ≤ (1 - Phi (x / s)) * Real.exp (Hz (x / s) * x / (2 * s ^ 3) * (sp ^ 2 - s ^ 2) +
        (1 / m ^ 5 + 10 / m ^ 6) * (x ^ 2 + 1) * (sp ^ 2 - s ^ 2) ^ 2) ∧
    (1 - Phi (x / s)) * Real.exp (Hz (x / s) * x / (2 * s ^ 3) * (sp ^ 2 - s ^ 2) -
        (1 / m ^ 5 + 10 / m ^ 6) * (x ^ 2 + 1) * (sp ^ 2 - s ^ 2) ^ 2) ≤ 1 - Phi (x / sp) := by
  have hfact := @EthierKurtz.gaussian_tail_variance_perturbation
  apply hfact <;> assumption

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
    linarith [sq_nonneg (∫ ω, ξ i ω ^ 2 ∂P)]
  have hsumv : ∑ i, variance (fun ω => ξ i ω ^ 2) P ≤ δ ^ 2 := by
    calc ∑ i, variance (fun ω => ξ i ω ^ 2) P ≤ ∑ i, δ ^ 2 * ∫ ω, ξ i ω ^ 2 ∂P :=
          Finset.sum_le_sum fun i _ => hvi2 i
      _ = δ ^ 2 := by rw [← Finset.mul_sum, h1, mul_one]
  refine ⟨hEQ, hW2, by linarith, ?_⟩
  rw [← hVQ0, hVQ]; exact hsumv

end Prob

end P99bcb804

end X34_BdBE

section X39_Delta

/-! KMT 1976 II, (4.4)/(4.7): abstract averaging layer over a finite uniform space `Ω`
(later `Ω = Perm (Fin N ⊕ Fin N)`, `η = etaV x`). -/

open Finset Real

namespace P99bcb804

variable {Ω : Type} [Fintype Ω]

lemma exp_two_mul_eq_sq (z : ℝ) : exp (2 * z) = exp z ^ 2 := by
  rw [sq, ← exp_add]; ring_nf

/-- Cauchy–Schwarz for sums of exponentials. -/
lemma cs_exp (f g : Ω → ℝ) :
    (∑ ω, exp (f ω + g ω)) ^ 2 ≤ (∑ ω, exp (2 * f ω)) * ∑ ω, exp (2 * g ω) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun ω => exp (f ω)) (fun ω => exp (g ω))
  simp only [exp_add, exp_two_mul_eq_sq]
  exact h

/-- Jensen for `exp` over a uniform finite average. -/
lemma jensen_exp [Nonempty Ω] (f : Ω → ℝ) :
    (Fintype.card Ω : ℝ) * exp ((∑ ω, f ω) / Fintype.card Ω) ≤ ∑ ω, exp (f ω) := by
  set n : ℝ := (Fintype.card Ω : ℝ) with hndef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast Fintype.card_pos
  set m := (∑ ω, f ω) / n with hmdef
  have h : ∀ ω, exp m * (1 + (f ω - m)) ≤ exp (f ω) := fun ω => by
    have := add_one_le_exp (f ω - m)
    calc exp m * (1 + (f ω - m)) ≤ exp m * exp (f ω - m) :=
          mul_le_mul_of_nonneg_left (by linarith) (exp_pos m).le
      _ = exp (f ω) := by rw [← exp_add]; ring_nf
  have hs : ∑ ω, (1 + (f ω - m)) = n := by
    rw [sum_add_distrib, sum_sub_distrib]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
    rw [← hndef, hmdef]; field_simp; ring
  calc n * exp m = exp m * ∑ ω, (1 + (f ω - m)) := by rw [hs]; ring
    _ = ∑ ω, exp m * (1 + (f ω - m)) := by rw [mul_sum]
    _ ≤ ∑ ω, exp (f ω) := sum_le_sum fun ω _ => h ω

/-- The mean of `η` is `O(1/r)` when its mgf is `≤ exp(D t² + D'|t|/r)`. -/
lemma mean_abs_le [Nonempty Ω] (η : Ω → ℝ) {D D' r : ℝ} (hr : 0 < r)
    (hm : ∀ t : ℝ, ∑ ω, exp (t * η ω) ≤ (Fintype.card Ω : ℝ) * exp (D * t ^ 2 + D' * |t| / r)) :
    |(∑ ω, η ω) / Fintype.card Ω| ≤ (D + D') / r := by
  set n : ℝ := (Fintype.card Ω : ℝ) with hndef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast Fintype.card_pos
  set μ := (∑ ω, η ω) / n with hμ
  have key : ∀ t : ℝ, t * μ ≤ D * t ^ 2 + D' * |t| / r := by
    intro t
    have h1 := jensen_exp (fun ω => t * η ω)
    have h2 := (h1.trans (hm t))
    rw [← hndef, mul_le_mul_iff_right₀ hn, exp_le_exp, ← mul_sum] at h2
    rw [hμ]; rw [mul_div_assoc] at h2; exact h2
  have h1 := key (1 / r)
  have h2 := key (-(1 / r))
  have ha : |1 / r| = 1 / r := abs_of_pos (by positivity)
  rw [abs_neg, ha] at h2
  rw [ha] at h1
  have e1 : D * (1 / r) ^ 2 + D' * (1 / r) / r = (D + D') / r * (1 / r) := by ring
  have e2 : D * (-(1 / r)) ^ 2 + D' * (1 / r) / r = (D + D') / r * (1 / r) := by ring
  rw [e1] at h1; rw [e2] at h2
  have hr1 : 0 < 1 / r := by positivity
  rw [abs_le]; constructor
  · have : -μ * (1 / r) ≤ (D + D') / r * (1 / r) := by linarith
    have := le_of_mul_le_mul_right this hr1; linarith
  · have : μ * (1 / r) ≤ (D + D') / r * (1 / r) := by linarith
    exact le_of_mul_le_mul_right this hr1

/-- Upper half of (4.7): Cauchy–Schwarz splits the linear and quadratic parts. -/
theorem delta_upper (η R : Ω → ℝ) (good : Ω → Prop) [DecidablePred good] {α L c1 c2 cA : ℝ}
    (hcA : 0 ≤ cA)
    (hR : ∀ ω, good ω → R ω ≤ exp (α * η ω + L * η ω ^ 2))
    (hm : ∑ ω, exp (2 * (α * η ω)) ≤ cA * exp c1)
    (hq : ∑ ω, exp (2 * (L * η ω ^ 2)) ≤ cA * exp c2) :
    ∑ ω ∈ univ.filter good, R ω ≤ cA * exp ((c1 + c2) / 2) := by
  have h1 : ∑ ω ∈ univ.filter good, R ω ≤ ∑ ω, exp (α * η ω + L * η ω ^ 2) :=
    calc ∑ ω ∈ univ.filter good, R ω ≤ ∑ ω ∈ univ.filter good, exp (α * η ω + L * η ω ^ 2) :=
          sum_le_sum fun ω hω => hR ω (mem_filter.1 hω).2
      _ ≤ ∑ ω, exp (α * η ω + L * η ω ^ 2) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => (exp_pos _).le
  have h2 := cs_exp (fun ω => α * η ω) (fun ω => L * η ω ^ 2)
  have h3 : (∑ ω, exp (α * η ω + L * η ω ^ 2)) ^ 2 ≤ (cA * exp ((c1 + c2) / 2)) ^ 2 := by
    refine h2.trans ((mul_le_mul hm hq (sum_nonneg fun _ _ => (exp_pos _).le)
      (by positivity)).trans (le_of_eq ?_))
    rw [mul_pow, ← exp_two_mul_eq_sq, show 2 * ((c1 + c2) / 2) = c1 + c2 by ring, exp_add]; ring
  exact h1.trans ((pow_le_pow_iff_left₀ (sum_nonneg fun _ _ => (exp_pos _).le) (by positivity)
    two_ne_zero).1 h3)

/-- Lower half of (4.7): Cauchy–Schwarz + Jensen, minus the bad set. -/
theorem delta_lower (η R : Ω → ℝ) (good : Ω → Prop) [DecidablePred good] {α L c0 c3 b cA : ℝ}
    (hcA : 0 < cA)
    (hR : ∀ ω, good ω → exp (α * η ω - L * η ω ^ 2) ≤ R ω)
    (hjen : cA * exp (-c0) ≤ ∑ ω, exp (α * η ω))
    (hup : ∑ ω, exp (α * η ω + L * η ω ^ 2) ≤ cA * exp c3)
    (hbad : ∑ ω ∈ univ.filter (fun ω => ¬ good ω), exp (α * η ω - L * η ω ^ 2) ≤ cA * b) :
    cA * (exp (-(2 * c0) - c3) - b) ≤ ∑ ω ∈ univ.filter good, R ω := by
  set Sm := ∑ ω, exp (α * η ω - L * η ω ^ 2) with hSm
  set Sp := ∑ ω, exp (α * η ω + L * η ω ^ 2) with hSp
  have hSp0 : 0 < Sp := by
    have : Nonempty Ω := by
      by_contra h
      rw [not_nonempty_iff] at h
      have : ∑ ω, exp (α * η ω) = 0 := by simp
      have := hjen; rw [‹∑ ω, exp (α * η ω) = 0›] at this
      have : 0 < cA * exp (-c0) := by positivity
      linarith
    exact sum_pos (fun _ _ => exp_pos _) univ_nonempty
  have hcs := cs_exp (fun ω => (α * η ω - L * η ω ^ 2) / 2) (fun ω => (α * η ω + L * η ω ^ 2) / 2)
  have e1 : ∀ ω, (α * η ω - L * η ω ^ 2) / 2 + (α * η ω + L * η ω ^ 2) / 2 = α * η ω :=
    fun ω => by ring
  have e2 : ∀ ω, 2 * ((α * η ω - L * η ω ^ 2) / 2) = α * η ω - L * η ω ^ 2 := fun ω => by ring
  have e3 : ∀ ω, 2 * ((α * η ω + L * η ω ^ 2) / 2) = α * η ω + L * η ω ^ 2 := fun ω => by ring
  simp only [e1, e2, e3] at hcs
  -- (cA e^{-c0})² ≤ Sm * Sp ≤ Sm * cA e^{c3}
  have hj2 : (cA * exp (-c0)) ^ 2 ≤ Sm * (cA * exp c3) := by
    have hpos : 0 ≤ cA * exp (-c0) := by positivity
    have hSm0 : 0 ≤ Sm := sum_nonneg fun _ _ => (exp_pos _).le
    calc (cA * exp (-c0)) ^ 2 ≤ (∑ ω, exp (α * η ω)) ^ 2 := pow_le_pow_left₀ hpos hjen 2
      _ ≤ Sm * Sp := hcs
      _ ≤ Sm * (cA * exp c3) := mul_le_mul_of_nonneg_left hup hSm0
  have hmain : cA * exp (-(2 * c0) - c3) ≤ Sm := by
    have hc : 0 < cA * exp c3 := by positivity
    have e : cA * exp (-(2 * c0) - c3) = (cA * exp (-c0)) ^ 2 / (cA * exp c3) := by
      rw [eq_div_iff hc.ne', mul_pow, ← exp_two_mul_eq_sq]
      rw [show cA * exp (-(2 * c0) - c3) * (cA * exp c3) = cA ^ 2 * (exp (-(2 * c0) - c3) * exp c3) by
        ring, ← exp_add]
      ring_nf
    rw [e, div_le_iff₀ hc]; linarith
  have hsplit : Sm = ∑ ω ∈ univ.filter good, exp (α * η ω - L * η ω ^ 2) +
      ∑ ω ∈ univ.filter (fun ω => ¬ good ω), exp (α * η ω - L * η ω ^ 2) :=
    (sum_filter_add_sum_filter_not univ good _).symm
  have hgood : ∑ ω ∈ univ.filter good, exp (α * η ω - L * η ω ^ 2) ≤
      ∑ ω ∈ univ.filter good, R ω := sum_le_sum fun ω hω => hR ω (mem_filter.1 hω).2
  rw [mul_sub]; linarith

end P99bcb804

end X39_Delta

section X40_L4

/-! KMT 1976 Part II, Lemma 4 (p.46): for `Σ aᵢ = 0`, `|aᵢ| ≤ A` and a uniformly random
permutation `w`, `E exp(t Σ aᵢ d_{w i}) ≤ exp(t² A² Σ dᵢ²)`.
Proof: swap-symmetrisation for balanced `{-1,0,1}` vectors (pairs `(i, e i)`), then
Krein–Milman + convexity (the extreme points of `{Σ b = 0, |bᵢ| ≤ 1}` are balanced, Lemma 5). -/

open Finset Real

namespace P99bcb804

variable {α : Type} [Fintype α] [DecidableEq α]

/-! ## Convexity / Krein–Milman reduction to balanced vectors. -/

/-! ## The quadratic exponential bound ("consequently" part of Lemma 4). -/

open MeasureTheory ProbabilityTheory in
lemma pdf_mul_exp_sq' (l x : ℝ) :
    gaussianPDFReal 0 1 x * exp (l * x ^ 2) = (√(2 * π))⁻¹ * exp (-(1 / 2 - l) * x ^ 2) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2; ring

open MeasureTheory ProbabilityTheory in
/-- Exponential moment of a squared standard Gaussian. -/
theorem gauss_sq_mgf' {l : ℝ} (hl : l < 1 / 2) :
    Integrable (fun x => exp (l * x ^ 2)) (gaussianReal 0 1) ∧
      ∫ x, exp (l * x ^ 2) ∂gaussianReal 0 1 = (√(1 - 2 * l))⁻¹ := by
  have hb : 0 < 1 / 2 - l := by linarith
  constructor
  · rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    have : (fun x => (gaussianPDF 0 1 x).toReal • exp (l * x ^ 2)) =
        fun x => (√(2 * π))⁻¹ * exp (-(1 / 2 - l) * x ^ 2) := by
      funext x
      rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul,
        pdf_mul_exp_sq']
    rw [this]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp_rw [smul_eq_mul, pdf_mul_exp_sq']
    rw [integral_const_mul, integral_gaussian]
    have h1 : 0 < 1 - 2 * l := by linarith
    have e : π / (1 / 2 - l) = 2 * π / (1 - 2 * l) := by field_simp
    rw [e, Real.sqrt_div' _ h1.le]
    have h2 : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
    have h3 : 0 < √(1 - 2 * l) := Real.sqrt_pos.mpr h1
    field_simp

open MeasureTheory ProbabilityTheory in
/-- A sub-Gaussian moment generating function bound `Σ e^{tX} ≤ C e^{t² D}` gives
`Σ e^{u X²/D} ≤ C (1-4u)^{-1/2}` for `0 ≤ u < 1/4` (Gaussian linearisation). -/
theorem sq_exp_of_mgf {ι : Type} [Fintype ι] (X : ι → ℝ) {D C : ℝ} (hD : 0 < D)
    (hmgf : ∀ t : ℝ, ∑ i, exp (t * X i) ≤ C * exp (t ^ 2 * D)) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u < 1 / 4) :
    ∑ i, exp (u * X i ^ 2 / D) ≤ C * (√(1 - 4 * u))⁻¹ := by
  set s := √(2 * u / D) with hs
  have hs2 : s ^ 2 = 2 * u / D := Real.sq_sqrt (by positivity)
  have hlin : ∀ i, exp (u * X i ^ 2 / D) = ∫ z, exp ((s * X i) * z) ∂gaussianReal 0 1 := by
    intro i
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (s * X i)
    simp only [mgf, id, zero_mul, zero_add, NNReal.coe_one, one_mul] at h
    rw [h]; congr 1
    rw [mul_pow, hs2]; field_simp
  have hint : ∀ i, Integrable (fun z => exp ((s * X i) * z)) (gaussianReal 0 1) := fun i =>
    integrable_exp_mul_gaussianReal (s * X i)
  have hq := gauss_sq_mgf' (l := 2 * u) (by linarith)
  calc ∑ i, exp (u * X i ^ 2 / D) = ∑ i, ∫ z, exp ((s * X i) * z) ∂gaussianReal 0 1 :=
        Finset.sum_congr rfl fun i _ => hlin i
    _ = ∫ z, ∑ i, exp ((s * z) * X i) ∂gaussianReal 0 1 := by
        rw [← integral_finsetSum _ fun i _ => hint i]
        congr 1; funext z; exact Finset.sum_congr rfl fun i _ => by ring_nf
    _ ≤ ∫ z, C * exp ((2 * u) * z ^ 2) ∂gaussianReal 0 1 := by
        refine integral_mono (integrable_finsetSum _ fun i _ => ?_) (hq.1.const_mul C) fun z => ?_
        · simpa [mul_comm, mul_left_comm, mul_assoc] using hint i
        · refine (hmgf (s * z)).trans (le_of_eq ?_)
          congr 2
          rw [mul_pow, hs2]; field_simp
    _ = C * (√(1 - 4 * u))⁻¹ := by
        rw [integral_const_mul, hq.2]; congr 3; ring

/-! ## KMT (4.9): the cross-product statistic `η` is sub-Gaussian. Population indexed by
`Fin N ⊕ Fin N` (first half `inl`, second half `inr`). -/

/-- `η = -(1/√N) Σᵢ x_{w(inl i)} x_{w(inr i)}` (KMT 1976 II, p.44, with `Σ x = 0`). -/
noncomputable def etaV {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) : ℝ :=
  -(1 / √(N : ℝ)) * ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i))

lemma inv_sqrt_le_exp {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) : (√(1 - 4 * u))⁻¹ ≤ exp (4 * u) := by
  set v := 4 * u with hv
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 / 2 := by linarith
  have hpos : 0 < √(1 - v) := Real.sqrt_pos.2 (by linarith)
  have h1 : 1 ≤ (1 - v) * exp (2 * v) := by nlinarith [add_one_le_exp (2 * v)]
  have h2 : √(1 - v) * exp v = √((1 - v) * exp (2 * v)) := by
    rw [Real.sqrt_mul (by linarith), show exp (2 * v) = exp v ^ 2 by rw [← exp_nat_mul]; ring_nf,
      Real.sqrt_sq (exp_pos v).le]
  have h3 : 1 ≤ √(1 - v) * exp v := by
    rw [h2]; calc (1 : ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h1
  rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith

/-- **KMT 1976 II, (4.9)** (with explicit constant): for `Σ x = 0`, `|xᵢ| ≤ K`,
`1/√N ≤ |t| ≤ √N/(16K²)`: `E e^{tη} ≤ exp((2K² + 4K⁴) t²)`. -/
theorem eta_mgf {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K : ℝ} (hK : 0 < K)
    (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) (t : ℝ) (ht1 : 1 ≤ |t| * √(N : ℝ))
    (ht2 : |t| * (16 * K ^ 2) ≤ √(N : ℝ)) :
    ∑ w : Equiv.Perm (Fin N ⊕ Fin N), exp (t * etaV x w) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp ((2 * K ^ 2 + 4 * K ^ 4) * t ^ 2) := by
  have hfact := @EthierKurtz.kmt_permutation_bilinear_mgf
  apply hfact <;> assumption

/-- **KMT 1976 II, (4.3)** (Chernoff from (4.9)): the cross sum `Σ x_{w(inl i)} x_{w(inr i)}`
exceeds `c N` only for an exponentially small fraction of permutations. -/
theorem cross_tail {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K : ℝ} (hK : 0 < K)
    (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ)
    (hδ1 : δ * (16 * K ^ 2) ≤ 1) (hδ2 : δ * (2 * K ^ 2 + 4 * K ^ 4) ≤ c / 2)
    (hδN : 1 ≤ δ * N) :
    ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) =>
        c * N ≤ ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i)))).card : ℝ) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (-(δ * c / 2) * N) := by
  classical
  set n : ℝ := (N : ℝ) with hndef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast hN
  set r := √n with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hn
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn.le
  set t := -(δ * r) with htdef
  have htabs : |t| = δ * r := by rw [htdef, abs_neg, abs_of_pos (by positivity)]
  have hmgf := eta_mgf hN x hK hx hs t (by rw [htabs]; nlinarith) (by rw [htabs]; nlinarith)
  set C := 2 * K ^ 2 + 4 * K ^ 4 with hC
  have hpt : ∀ w : Equiv.Perm (Fin N ⊕ Fin N),
      (if c * n ≤ ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i)) then (1 : ℝ) else 0) ≤
        exp (t * etaV x w - δ * c * n) := by
    intro w
    split_ifs with h
    · rw [← exp_zero]
      apply exp_le_exp.2
      have he : etaV x w = -(1 / r) * ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i)) := by
        simp [etaV, hrdef, hndef]
      rw [he, htdef]
      have e : -(δ * r) * (-(1 / r) * ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i)))
          = δ * ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i)) := by field_simp
      rw [e]
      linarith [mul_le_mul_of_nonneg_left h hδ0.le]
    · exact (exp_pos _).le
  rw [Finset.natCast_card_filter]
  calc ∑ w, (if c * n ≤ ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i)) then (1 : ℝ) else 0)
      ≤ ∑ w, exp (t * etaV x w - δ * c * n) := sum_le_sum fun w _ => hpt w
    _ = exp (-(δ * c * n)) * ∑ w, exp (t * etaV x w) := by
        rw [mul_sum]; refine sum_congr rfl fun w _ => ?_
        rw [← exp_add]; congr 1; ring
    _ ≤ exp (-(δ * c * n)) * ((Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (C * t ^ 2)) :=
        mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ ≤ (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (-(δ * c / 2) * n) := by
        rw [mul_left_comm, ← exp_add]
        refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
        have ht2 : t ^ 2 = δ ^ 2 * n := by rw [htdef, neg_sq, mul_pow, hr2]
        rw [ht2]
        have : C * (δ ^ 2 * n) ≤ c / 2 * δ * n := by
          have := mul_le_mul_of_nonneg_right hδ2 (by positivity : (0 : ℝ) ≤ δ * n)
          linarith
        linarith

/-! ## KMT (4.10): `E e^{v η²} ≤ e^{C v}` for small `v`, uniformly in `N`. -/

lemma eta_abs_le {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K : ℝ}
    (hx : ∀ i, |x i| ≤ K) (w : Equiv.Perm (Fin N ⊕ Fin N)) :
    |etaV x w| ≤ K ^ 2 * √(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < √(N : ℝ) := Real.sqrt_pos.2 hn
  have hK : 0 ≤ K := (abs_nonneg _).trans (hx (Sum.inl ⟨0, hN⟩))
  have hsum : |∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i))| ≤ N * K ^ 2 := by
    calc _ ≤ ∑ i, |x (w (Sum.inl i)) * x (w (Sum.inr i))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, K ^ 2 := sum_le_sum fun i _ => by
          rw [abs_mul, sq]; exact mul_le_mul (hx _) (hx _) (abs_nonneg _) hK
      _ = N * K ^ 2 := by simp
  rw [etaV, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / √(N : ℝ))]
  calc 1 / √(N : ℝ) * |∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i))|
        ≤ 1 / √(N : ℝ) * (N * K ^ 2) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = K ^ 2 * ((N : ℝ) / √(N : ℝ)) := by ring
    _ = K ^ 2 * √(N : ℝ) := by rw [Real.div_sqrt]

/-- (4.9) extended to all `t` (crude bound `|η| ≤ K²√N` outside the window), at the cost of
a factor `e^{K²}` and the larger variance proxy `D = 2K² + 20K⁴`. -/
theorem eta_mgf_all {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K : ℝ} (hK : 0 < K)
    (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) (t : ℝ) :
    ∑ w : Equiv.Perm (Fin N ⊕ Fin N), exp (t * etaV x w) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (K ^ 2) *
        exp (t ^ 2 * (2 * K ^ 2 + 20 * K ^ 4)) := by
  set cA : ℝ := (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) with hcAdef
  set r := √(N : ℝ) with hrdef
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < r := Real.sqrt_pos.2 hn
  have hcA : 0 ≤ cA := by positivity
  have crude : ∀ w, exp (t * etaV x w) ≤ exp (|t| * (K ^ 2 * r)) := fun w =>
    exp_le_exp.2 (by
      calc t * etaV x w ≤ |t * etaV x w| := le_abs_self _
        _ = |t| * |etaV x w| := abs_mul _ _
        _ ≤ |t| * (K ^ 2 * r) := mul_le_mul_of_nonneg_left (eta_abs_le hN x hx w) (abs_nonneg _))
  have hsumc : ∀ B : ℝ, (∀ w, exp (t * etaV x w) ≤ B) → ∑ w, exp (t * etaV x w) ≤ cA * B := by
    intro B hB
    calc _ ≤ ∑ _w : Equiv.Perm (Fin N ⊕ Fin N), B := sum_le_sum fun w _ => hB w
      _ = cA * B := by simp [cA]
  have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
  have hD0 : 0 ≤ t ^ 2 * (2 * K ^ 2 + 20 * K ^ 4) := by positivity
  by_cases h1 : 1 ≤ |t| * r
  · by_cases h2 : |t| * (16 * K ^ 2) ≤ r
    · calc _ ≤ cA * exp ((2 * K ^ 2 + 4 * K ^ 4) * t ^ 2) := eta_mgf hN x hK hx hs t h1 h2
        _ ≤ _ := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hcA
          rw [← exp_add]; refine exp_le_exp.2 ?_
          have : 0 ≤ t ^ 2 * K ^ 4 := by positivity
          linarith [sq_nonneg K]
    · push_neg at h2
      refine (hsumc _ fun w => crude w).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hcA
      rw [← exp_add]; refine exp_le_exp.2 ?_
      have ht : 0 ≤ |t| * K ^ 2 := by positivity
      have h3 := mul_le_mul_of_nonneg_left h2.le ht
      have : 0 ≤ t ^ 2 * K ^ 4 := by positivity
      have h4 : |t| ^ 2 * K ^ 4 = t ^ 2 * K ^ 4 := by rw [hsq]
      have h5 : 0 ≤ t ^ 2 * K ^ 2 := by positivity
      have h6 : 0 ≤ K ^ 2 := by positivity
      linarith
  · push_neg at h1
    refine (hsumc _ fun w => crude w).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hcA
    rw [← exp_add]; refine exp_le_exp.2 ?_
    have h3 := mul_le_mul_of_nonneg_left h1.le (sq_nonneg K)
    linarith

/-- Gaussian linearisation of `eta_mgf_all`. -/
theorem eta_sq_exp {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K : ℝ} (hK : 0 < K)
    (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) {u : ℝ} (hu0 : 0 ≤ u) (hu : u < 1 / 4) :
    ∑ w : Equiv.Perm (Fin N ⊕ Fin N), exp (u * etaV x w ^ 2 / (2 * K ^ 2 + 20 * K ^ 4)) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (K ^ 2) * (√(1 - 4 * u))⁻¹ :=
  sq_exp_of_mgf (fun w => etaV x w) (by positivity) (eta_mgf_all hN x hK hx hs) hu0 hu

/-- **KMT 1976 II, (4.10)**: with `D = 2K² + 20K⁴`, for `0 ≤ v` and `8Dv ≤ 1`,
`Σ_w e^{v η²} ≤ N!·exp(8D(e^{K²+1/2} - 1) v)`. -/
theorem eta_sq_lin {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K : ℝ} (hK : 0 < K)
    (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) {v : ℝ} (hv0 : 0 ≤ v)
    (hv : v * (8 * (2 * K ^ 2 + 20 * K ^ 4)) ≤ 1) :
    ∑ w : Equiv.Perm (Fin N ⊕ Fin N), exp (v * etaV x w ^ 2) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) *
        exp (v * (8 * (2 * K ^ 2 + 20 * K ^ 4) * (exp (K ^ 2 + 1 / 2) - 1))) := by
  have hM := eta_sq_exp hN x hK hx hs (u := 1 / 8) (by norm_num) (by norm_num)
  have hinv := inv_sqrt_le_exp (u := 1 / 8) (by norm_num) le_rfl
  set D := 2 * K ^ 2 + 20 * K ^ 4 with hDdef
  have hD : 0 < D := by positivity
  set cA : ℝ := (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) with hcAdef
  have hcA : 0 ≤ cA := by positivity
  set l := v * (8 * D) with hl
  have hl0 : 0 ≤ l := by positivity
  set M := exp (K ^ 2 + 1 / 2) with hMdef
  have hM' : ∑ w : Equiv.Perm (Fin N ⊕ Fin N), exp (1 / 8 * etaV x w ^ 2 / D) ≤ cA * M := by
    refine hM.trans ?_
    rw [mul_assoc, hMdef, exp_add]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hinv.trans ?_) (exp_pos _).le) hcA
    norm_num
  have hpt : ∀ w, exp (v * etaV x w ^ 2) ≤ (1 - l) + l * exp (1 / 8 * etaV x w ^ 2 / D) := by
    intro w
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 / 8 * etaV x w ^ 2 / D))
      (by linarith : 0 ≤ 1 - l) hl0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
    have e : l * (1 / 8 * etaV x w ^ 2 / D) = v * etaV x w ^ 2 := by
      rw [hl]; field_simp
    rw [e] at h
    exact h
  have e : l * (M - 1) = v * (8 * D * (M - 1)) := by rw [hl]; ring
  have hexp := add_one_le_exp (v * (8 * D * (M - 1)))
  calc ∑ w, exp (v * etaV x w ^ 2) ≤ ∑ w, ((1 - l) + l * exp (1 / 8 * etaV x w ^ 2 / D)) :=
        sum_le_sum fun w _ => hpt w
    _ = cA * (1 - l) + l * ∑ w, exp (1 / 8 * etaV x w ^ 2 / D) := by
        rw [sum_add_distrib, ← mul_sum]; simp [cA]; ring
    _ ≤ cA * (1 - l) + l * (cA * M) := by gcongr
    _ = cA * (1 + l * (M - 1)) := by ring
    _ ≤ cA * exp (v * (8 * D * (M - 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ hcA
        linarith

lemma exp_sub_one_le_mul_exp (z : ℝ) : exp z - 1 ≤ z * exp z := by
  have h := add_one_le_exp (-z)
  have h2 : exp (-z) * exp z = 1 := by rw [← exp_add]; simp
  linarith [mul_le_mul_of_nonneg_right h (exp_pos z).le, h2]

set_option maxHeartbeats 1000000 in
/-- Sharp form of (4.9)/(4.8) valid for **all** `t`: `E e^{tη} ≤ exp(D t² + D' |t|/√N)` with
`D = 2K² + 20K⁴`, `D' = 16K⁴ + D₁ e^{D₁}`, `D₁ = 2K² + 4K⁴`. Small `|t| < 1/√N` by convexity
from `t₀ = ±1/√N`. -/
theorem eta_mgf_sharp {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K : ℝ} (hK : 0 < K)
    (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) (t : ℝ) :
    ∑ w : Equiv.Perm (Fin N ⊕ Fin N), exp (t * etaV x w) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) *
        exp ((2 * K ^ 2 + 20 * K ^ 4) * t ^ 2 +
          (16 * K ^ 4 + (2 * K ^ 2 + 4 * K ^ 4) * exp (2 * K ^ 2 + 4 * K ^ 4)) * |t| / √(N : ℝ)) := by
  set D1 := 2 * K ^ 2 + 4 * K ^ 4 with hD1
  have hD10 : 0 ≤ D1 := by positivity
  set cA : ℝ := (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) with hcAdef
  set r := √(N : ℝ) with hrdef
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < r := Real.sqrt_pos.2 hn
  have hr2 : r ^ 2 = N := Real.sq_sqrt hn.le
  have hcA : 0 ≤ cA := by positivity
  have crude : ∀ w, exp (t * etaV x w) ≤ exp (|t| * (K ^ 2 * r)) := fun w =>
    exp_le_exp.2 (by
      calc t * etaV x w ≤ |t * etaV x w| := le_abs_self _
        _ = |t| * |etaV x w| := abs_mul _ _
        _ ≤ |t| * (K ^ 2 * r) := mul_le_mul_of_nonneg_left (eta_abs_le hN x hx w) (abs_nonneg _))
  have hsumc : ∀ B : ℝ, (∀ w, exp (t * etaV x w) ≤ B) → ∑ w, exp (t * etaV x w) ≤ cA * B := by
    intro B hB
    calc _ ≤ ∑ _w : Equiv.Perm (Fin N ⊕ Fin N), B := sum_le_sum fun w _ => hB w
      _ = cA * B := by simp [cA]
  have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
  have hta : 0 ≤ |t| := abs_nonneg t
  set E := (2 * K ^ 2 + 20 * K ^ 4) * t ^ 2 + (16 * K ^ 4 + D1 * exp D1) * |t| / r with hE
  have hT1 : 0 ≤ (2 * K ^ 2 + 20 * K ^ 4) * t ^ 2 := by positivity
  have hT2 : 0 ≤ (16 * K ^ 4 + D1 * exp D1) * |t| / r := by positivity
  have viaCrude : |t| * (K ^ 2 * r) ≤ E → ∑ w, exp (t * etaV x w) ≤ cA * exp E := fun h =>
    hsumc _ fun w => (crude w).trans (exp_le_exp.2 h)
  by_cases hb : r < |t| * (16 * K ^ 2)
  · apply viaCrude
    have h3 := mul_le_mul_of_nonneg_left hb.le (by positivity : 0 ≤ |t| * K ^ 2)
    have h4 : |t| ^ 2 * K ^ 4 = t ^ 2 * K ^ 4 := by rw [hsq]
    have h5 : 0 ≤ t ^ 2 * K ^ 2 := by positivity
    have h6 : 0 ≤ t ^ 2 * K ^ 4 := by positivity
    rw [hE]; linarith
  push_neg at hb
  by_cases ha : 1 ≤ |t| * r
  · calc _ ≤ cA * exp (D1 * t ^ 2) := eta_mgf hN x hK hx hs t ha hb
      _ ≤ cA * exp E := by
        refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) hcA
        have : 0 ≤ t ^ 2 * K ^ 4 := by positivity
        rw [hE, hD1]; linarith
  push_neg at ha
  by_cases hNs : (N : ℝ) < 16 * K ^ 2
  · apply viaCrude
    have key : |t| * (K ^ 2 * r) ≤ 16 * K ^ 4 * |t| / r := by
      rw [le_div_iff₀ hr]
      have : |t| * (K ^ 2 * r) * r = |t| * K ^ 2 * N := by rw [← hr2]; ring
      rw [this]
      have h7 := mul_le_mul_of_nonneg_left hNs.le (by positivity : 0 ≤ |t| * K ^ 2)
      linarith
    have key2 : 16 * K ^ 4 * |t| / r ≤ (16 * K ^ 4 + D1 * exp D1) * |t| / r := by
      apply div_le_div_of_nonneg_right _ hr.le
      have : 0 ≤ D1 * exp D1 * |t| := by positivity
      have e : (16 * K ^ 4 + D1 * exp D1) * |t| = 16 * K ^ 4 * |t| + D1 * exp D1 * |t| := by ring
      rw [e]; linarith
    rw [hE]; linarith
  push_neg at hNs
  set s0 : ℝ := if 0 ≤ t then 1 else -1 with hs0
  have hs0a : |s0| = 1 := by rw [hs0]; split_ifs <;> simp
  set t0 := s0 / r with ht0
  set l := |t| * r with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l < 1 := ha
  have htl : t = l * t0 := by
    rw [hl, ht0, hs0]
    split_ifs with h
    · rw [abs_of_nonneg h]; field_simp
    · push_neg at h; rw [abs_of_neg h]; field_simp
  have ht0a : |t0| = 1 / r := by rw [ht0, abs_div, hs0a, abs_of_pos hr]
  have hm := eta_mgf hN x hK hx hs t0 (by rw [ht0a]; field_simp; rfl)
    (by
      rw [ht0a, div_mul_eq_mul_div, one_mul, div_le_iff₀ hr]
      linarith)
  have ht0sq : t0 ^ 2 = 1 / N := by
    rw [← sq_abs, ht0a, div_pow, hr2]; ring
  rw [ht0sq] at hm
  have hpt : ∀ w, exp (t * etaV x w) ≤ (1 - l) + l * exp (t0 * etaV x w) := by
    intro w
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (t0 * etaV x w))
      (by linarith : 0 ≤ 1 - l) hl0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
    rw [htl, mul_assoc]; exact h
  set q := exp (D1 * (1 / N)) with hq
  have hsum : ∑ w, exp (t * etaV x w) ≤ cA * (1 + l * (q - 1)) := by
    calc ∑ w, exp (t * etaV x w) ≤ ∑ w, ((1 - l) + l * exp (t0 * etaV x w)) :=
          sum_le_sum fun w _ => hpt w
      _ = cA * (1 - l) + l * ∑ w, exp (t0 * etaV x w) := by
          rw [sum_add_distrib, ← mul_sum]; simp [cA]; ring
      _ ≤ cA * (1 - l) + l * (cA * q) := by gcongr
      _ = cA * (1 + l * (q - 1)) := by ring
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ hcA)
  refine (add_comm (l * (q - 1)) 1 ▸ add_one_le_exp (l * (q - 1))).trans (exp_le_exp.2 ?_)
  have hq1 : q - 1 ≤ D1 * (1 / N) * exp D1 := by
    refine (exp_sub_one_le_mul_exp _).trans ?_
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
    have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hn]; exact_mod_cast hN
    nlinarith
  have h8 : l * (q - 1) ≤ l * (D1 * (1 / N) * exp D1) := mul_le_mul_of_nonneg_left hq1 hl0
  have h9 : l * (D1 * (1 / N) * exp D1) = D1 * exp D1 * |t| / r := by
    rw [hl, ← hr2]; field_simp
  have h10 : D1 * exp D1 * |t| / r ≤ (16 * K ^ 4 + D1 * exp D1) * |t| / r := by
    apply div_le_div_of_nonneg_right _ hr.le
    have : 0 ≤ 16 * K ^ 4 * |t| := by positivity
    have e : (16 * K ^ 4 + D1 * exp D1) * |t| = 16 * K ^ 4 * |t| + D1 * exp D1 * |t| := by ring
    rw [e]; linarith
  rw [hE]; linarith

end P99bcb804

end X40_L4

section X41_Dperm

/-! KMT 1976 II, (4.7) instantiated for pairings `w : Perm (Fin N ⊕ Fin N)`:
the pair variance `sw2 x w = σ_w²/N` and the averaged Gaussian tail. Iteration file: imports the
helper modules `P99bcb804Mills/Delta/L4` (oleans built by scratch/probe/99bcb804_mods/build.sh). -/

open Finset Real

namespace P99bcb804

/-- Pair variance `σ_w²/N` for the pairing `(w (inl i), w (inr i))`. -/
noncomputable def sw2 {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) : ℝ :=
  (∑ i, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ 2) / N

lemma sw2_nonneg {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) :
    0 ≤ sw2 x w := by
  unfold sw2; positivity

lemma sum_sq_split {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) :
    ∑ i, x i ^ 2 = ∑ i, x (w (Sum.inl i)) ^ 2 + ∑ i, x (w (Sum.inr i)) ^ 2 := by
  rw [← Fintype.sum_sum_type (f := fun j => x (w j) ^ 2)]
  exact (Equiv.sum_comp w (fun j => x j ^ 2)).symm

lemma sw2_eq' {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) :
    sw2 x w = (∑ i, x i ^ 2 - 2 * ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i))) / N := by
  unfold sw2
  rw [sum_sq_split x w, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun i _ => by ring

lemma two_eta {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) :
    2 * etaV x w / √(N : ℝ) = -(2 * ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i))) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hn.le
  rw [eq_div_iff hn.ne']
  calc 2 * etaV x w / √(N : ℝ) * N
      = -(2 * ∑ i, x (w (Sum.inl i)) * x (w (Sum.inr i))) * (N / (√(N : ℝ) * √(N : ℝ))) := by
        unfold etaV; ring
    _ = _ := by rw [hsq, div_self hn.ne', mul_one]

lemma sw2_eq {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) (w : Equiv.Perm (Fin N ⊕ Fin N)) :
    sw2 x w = (∑ i, x i ^ 2) / N + 2 * etaV x w / √(N : ℝ) := by
  rw [sw2_eq', two_eta hN]; ring

/-- Pointwise tail ratio for a good pairing (KMT (4.5)-(4.6) with `s'² - s² = 2η/√N`). -/
lemma ratio_bd {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {c y : ℝ} (hc : 0 < c)
    (hcS : c * N ≤ ∑ i, x i ^ 2) (hy : 0 ≤ y) (w : Equiv.Perm (Fin N ⊕ Fin N))
    (hw : c / 2 ≤ sw2 x w) :
    1 - Phi (y / √(sw2 x w)) ≤ (1 - Phi (y / √((∑ i, x i ^ 2) / N))) *
        exp (Hz (y / √((∑ i, x i ^ 2) / N)) * y / (√((∑ i, x i ^ 2) / N) ^ 3 * √(N : ℝ)) * etaV x w
          + 4 * (1 / √(c / 2) ^ 5 + 10 / √(c / 2) ^ 6) * (y ^ 2 + 1) / N * etaV x w ^ 2) ∧
    (1 - Phi (y / √((∑ i, x i ^ 2) / N))) *
        exp (Hz (y / √((∑ i, x i ^ 2) / N)) * y / (√((∑ i, x i ^ 2) / N) ^ 3 * √(N : ℝ)) * etaV x w
          - 4 * (1 / √(c / 2) ^ 5 + 10 / √(c / 2) ^ 6) * (y ^ 2 + 1) / N * etaV x w ^ 2) ≤
      1 - Phi (y / √(sw2 x w)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < √(N : ℝ) := Real.sqrt_pos.2 hn
  have hm : 0 < √(c / 2) := Real.sqrt_pos.2 (by positivity)
  have hS : c ≤ (∑ i, x i ^ 2) / N := (le_div_iff₀ hn).2 hcS
  have hms : √(c / 2) ≤ √((∑ i, x i ^ 2) / N) := Real.sqrt_le_sqrt (by linarith)
  have hmsp : √(c / 2) ≤ √(sw2 x w) := Real.sqrt_le_sqrt hw
  obtain ⟨h1, h2⟩ := tail_ratio_lin hm hms hmsp hy
  have hs0 : 0 < √((∑ i, x i ^ 2) / N) := hm.trans_le hms
  have hs2 : √((∑ i, x i ^ 2) / N) ^ 2 = (∑ i, x i ^ 2) / N :=
    Real.sq_sqrt (div_nonneg (sum_nonneg fun i _ => sq_nonneg _) hn.le)
  have hsp2 : √(sw2 x w) ^ 2 = sw2 x w := Real.sq_sqrt (sw2_nonneg x w)
  have hd : √(sw2 x w) ^ 2 - √((∑ i, x i ^ 2) / N) ^ 2 = 2 * etaV x w / √(N : ℝ) := by
    rw [hsp2, hs2, sw2_eq hN]; ring
  have e1 : Hz (y / √((∑ i, x i ^ 2) / N)) * y / (2 * √((∑ i, x i ^ 2) / N) ^ 3) *
      (√(sw2 x w) ^ 2 - √((∑ i, x i ^ 2) / N) ^ 2) =
      Hz (y / √((∑ i, x i ^ 2) / N)) * y / (√((∑ i, x i ^ 2) / N) ^ 3 * √(N : ℝ)) * etaV x w := by
    rw [hd]; field_simp
  have e2 : (1 / √(c / 2) ^ 5 + 10 / √(c / 2) ^ 6) * (y ^ 2 + 1) *
      (√(sw2 x w) ^ 2 - √((∑ i, x i ^ 2) / N) ^ 2) ^ 2 =
      4 * (1 / √(c / 2) ^ 5 + 10 / √(c / 2) ^ 6) * (y ^ 2 + 1) / N * etaV x w ^ 2 := by
    rw [hd, div_pow, Real.sq_sqrt hn.le]; ring
  rw [e1, e2] at h1 h2
  exact ⟨h1, h2⟩

/-- Elementary size bounds used to absorb every error term into `(y³+1)/√n`. -/
lemma Ybd {n y : ℝ} (hn : 1 ≤ n) (hy : 0 ≤ y) (hyn : y ≤ √n) :
    y / n ≤ (y ^ 3 + 1) / √n ∧ y ^ 2 / n ≤ (y ^ 3 + 1) / √n ∧ y ^ 3 / n ≤ (y ^ 3 + 1) / √n ∧
    y ^ 4 / n ≤ (y ^ 3 + 1) / √n ∧ 1 / n ≤ (y ^ 3 + 1) / √n := by
  have hr1 : 1 ≤ √n := Real.one_le_sqrt.2 hn
  have hr0 : 0 < √n := by linarith
  have hnr : n = √n ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hy3 : 0 ≤ y ^ 3 := pow_nonneg hy 3
  have hrn : √n ≤ n := by nlinarith [hnr]
  have key : ∀ a : ℝ, 0 ≤ a → a ≤ y ^ 3 + 1 → a / n ≤ (y ^ 3 + 1) / √n := by
    intro a ha hay
    rw [div_le_div_iff₀ (by linarith) hr0]
    calc a * √n ≤ (y ^ 3 + 1) * √n := mul_le_mul_of_nonneg_right hay hr0.le
      _ ≤ (y ^ 3 + 1) * n := mul_le_mul_of_nonneg_left hrn (by positivity)
  have h1 : y ≤ y ^ 3 + 1 := by
    linarith [mul_nonneg hy (sq_nonneg (y - 1)), sq_nonneg (y - 1), sq_nonneg y]
  have h2 : y ^ 2 ≤ y ^ 3 + 1 := by
    linarith [mul_nonneg (sq_nonneg (y - 1)) (by linarith : (0 : ℝ) ≤ y + 1)]
  refine ⟨key y hy h1, key _ (by positivity) h2, key _ hy3 (by linarith), ?_,
    key 1 zero_le_one (by linarith)⟩
  rw [div_le_div_iff₀ (by linarith) hr0]
  have h4 : y ^ 4 ≤ y ^ 3 * √n := by
    have := mul_le_mul_of_nonneg_left hyn hy3; linarith
  calc y ^ 4 * √n ≤ y ^ 3 * √n * √n := mul_le_mul_of_nonneg_right h4 hr0.le
    _ = y ^ 3 * n := by rw [mul_assoc, Real.mul_self_sqrt (by linarith)]
    _ ≤ (y ^ 3 + 1) * n := by linarith

/-- Gaussian tail lower bound valid for all `z ≥ 0`. -/
lemma G_lower {z : ℝ} (hz : 0 ≤ z) : exp (-(1 / 2)) * phi z / (2 * (z + 1)) ≤ 1 - Phi z := by
  have he : exp (-(1 / 2) : ℝ) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  have he0 := exp_pos (-(1 / 2) : ℝ)
  have hp := phi_pos z
  rcases le_or_gt 1 z with h1 | h1
  · have hm := mills_lower (x := z) (by linarith)
    calc exp (-(1 / 2)) * phi z / (2 * (z + 1)) ≤ phi z / (2 * (z + 1)) :=
          div_le_div_of_nonneg_right (mul_le_of_le_one_left hp.le he) (by positivity)
      _ ≤ z * phi z / (1 + z ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith [mul_nonneg hp.le (show (0 : ℝ) ≤ z ^ 2 + 2 * z - 1 by nlinarith)]
      _ ≤ 1 - Phi z := hm
  · have hmono : Phi z ≤ Phi 1 := (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)).mono h1.le
    have hm1 := mills_lower (x := (1 : ℝ)) one_pos
    have hpz : phi z ≤ phi 0 := phi_le_phi_zero z
    have hp0 := phi_pos 0
    have hb : exp (-(1 / 2)) * phi z / (2 * (z + 1)) ≤ exp (-(1 / 2)) * phi 0 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [mul_le_mul_of_nonneg_left hpz he0.le, mul_nonneg (mul_nonneg he0.le hp0.le) hz]
    have h1' : (1 : ℝ) * phi 1 / (1 + 1 ^ 2) = exp (-(1 / 2)) * phi 0 / 2 := by
      rw [phi_one]; ring
    calc exp (-(1 / 2)) * phi z / (2 * (z + 1)) ≤ exp (-(1 / 2)) * phi 0 / 2 := hb
      _ = 1 * phi 1 / (1 + 1 ^ 2) := h1'.symm
      _ ≤ 1 - Phi 1 := hm1
      _ ≤ 1 - Phi z := by linarith

/-! Constants. -/
noncomputable def kD (K : ℝ) : ℝ := 2 * K ^ 2 + 20 * K ^ 4
noncomputable def kDp (K : ℝ) : ℝ :=
  16 * K ^ 4 + (2 * K ^ 2 + 4 * K ^ 4) * exp (2 * K ^ 2 + 4 * K ^ 4)
noncomputable def kB (c : ℝ) : ℝ := 1 / √(c / 2) ^ 5 + 10 / √(c / 2) ^ 6
noncomputable def kP (c y : ℝ) : ℝ := (1 / √c) ^ 3 * y + 16 * (1 / √c) ^ 4 * y ^ 2
noncomputable def kQ (c : ℝ) : ℝ := (1 / √c) ^ 3 + 16 * (1 / √c) ^ 4
noncomputable def kC1 (K c : ℝ) : ℝ :=
  4 * kD K * ((1 / √c) ^ 6 + 32 * (1 / √c) ^ 7 + 256 * (1 / √c) ^ 8) + 2 * kDp K * kQ c
noncomputable def kC2 (K c : ℝ) : ℝ := 128 * kB c * kD K * (exp (K ^ 2 + 1 / 2) - 1)
noncomputable def kC0 (K c : ℝ) : ℝ := (kD K + kDp K) * kQ c

lemma kD_pos {K : ℝ} (hK : 0 < K) : 0 < kD K := by unfold kD; positivity
lemma kDp_nonneg (K : ℝ) : 0 ≤ kDp K := by unfold kDp; positivity
lemma kB_pos {c : ℝ} (hc : 0 < c) : 0 < kB c := by
  have : 0 < √(c / 2) := Real.sqrt_pos.2 (by positivity)
  unfold kB; positivity
lemma kQ_nonneg (c : ℝ) : 0 ≤ kQ c := by unfold kQ; positivity
lemma kC1_nonneg {K c : ℝ} (hK : 0 < K) : 0 ≤ kC1 K c := by
  have := kD_pos hK; have := kDp_nonneg K; have := kQ_nonneg c
  unfold kC1; positivity
lemma kC2_nonneg {K c : ℝ} (hK : 0 < K) (hc : 0 < c) : 0 ≤ kC2 K c := by
  have := kD_pos hK; have := kB_pos hc
  have : 0 ≤ exp (K ^ 2 + 1 / 2) - 1 := by
    have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ K ^ 2 + 1 / 2); linarith
  unfold kC2; positivity
lemma kC0_nonneg {K c : ℝ} (hK : 0 < K) : 0 ≤ kC0 K c := by
  have := kD_pos hK; have := kDp_nonneg K; have := kQ_nonneg c
  unfold kC0; positivity

/-- `α = Hz(y/s) y/(s³ r)` is nonnegative and `α r ≤ P(y)`. -/
lemma alpha_bd {c s y r : ℝ} (hc : 0 < c) (hs : √c ≤ s) (hy : 0 ≤ y) (hr : 0 < r) :
    0 ≤ Hz (y / s) * y / (s ^ 3 * r) ∧ Hz (y / s) * y / (s ^ 3 * r) * r ≤ kP c y := by
  have hc' : 0 < √c := Real.sqrt_pos.2 hc
  have hs0 : 0 < s := hc'.trans_le hs
  have hHz0 := Hz_pos (y / s)
  refine ⟨div_nonneg (mul_nonneg hHz0.le hy) (by positivity), ?_⟩
  have hu : 1 / s ≤ 1 / √c := one_div_le_one_div_of_le hc' hs
  have hHz : Hz (y / s) ≤ 1 + 16 * (y / s) := Hz_le_lin (div_nonneg hy hs0.le)
  have e : Hz (y / s) * y / (s ^ 3 * r) * r = Hz (y / s) * y * (1 / s) ^ 3 := by
    field_simp
  rw [e]
  have h1 : Hz (y / s) ≤ 1 + 16 * (y * (1 / √c)) := by
    have : y / s ≤ y * (1 / √c) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hu hy
    linarith
  have h2 : (1 / s) ^ 3 ≤ (1 / √c) ^ 3 := pow_le_pow_left₀ (by positivity) hu 3
  have h3 : 0 ≤ 1 + 16 * (y * (1 / √c)) := by
    have : 0 ≤ y * (1 / √c) := mul_nonneg hy (by positivity)
    linarith
  calc Hz (y / s) * y * (1 / s) ^ 3 ≤ (1 + 16 * (y * (1 / √c))) * y * (1 / √c) ^ 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 hy) h2 (by positivity) (mul_nonneg h3 hy)
    _ = kP c y := by unfold kP; ring

lemma alpha_r_bd {c α y n r Y : ℝ} (hn : n = r ^ 2) (hr : 0 < r) (hαP : α * r ≤ kP c y)
    (Y1 : y / n ≤ Y) (Y2 : y ^ 2 / n ≤ Y) : α / r ≤ kQ c * Y := by
  have hn0 : 0 < n := by rw [hn]; positivity
  calc α / r = α * r / n := by rw [hn]; field_simp
    _ ≤ kP c y / n := div_le_div_of_nonneg_right hαP hn0.le
    _ = (1 / √c) ^ 3 * (y / n) + 16 * (1 / √c) ^ 4 * (y ^ 2 / n) := by unfold kP; ring
    _ ≤ (1 / √c) ^ 3 * Y + 16 * (1 / √c) ^ 4 * Y := by gcongr
    _ = kQ c * Y := by unfold kQ; ring

lemma c1_bd {K c α y n r Y : ℝ} (hn : n = r ^ 2) (hr : 0 < r) (hα0 : 0 ≤ α)
    (hαP : α * r ≤ kP c y) (Y1 : y / n ≤ Y) (Y2 : y ^ 2 / n ≤ Y) (Y3 : y ^ 3 / n ≤ Y)
    (Y4 : y ^ 4 / n ≤ Y) :
    (2 * K ^ 2 + 20 * K ^ 4) * (2 * α) ^ 2 +
      (16 * K ^ 4 + (2 * K ^ 2 + 4 * K ^ 4) * exp (2 * K ^ 2 + 4 * K ^ 4)) * |2 * α| / r ≤
      kC1 K c * Y := by
  have hn0 : 0 < n := by rw [hn]; positivity
  have hα2 : α ^ 2 ≤ ((1 / √c) ^ 6 + 32 * (1 / √c) ^ 7 + 256 * (1 / √c) ^ 8) * Y := by
    have e : α ^ 2 = (α * r) ^ 2 / n := by
      rw [hn, mul_pow, mul_div_assoc, div_self (by positivity), mul_one]
    have h1 : (α * r) ^ 2 ≤ kP c y ^ 2 := pow_le_pow_left₀ (mul_nonneg hα0 hr.le) hαP 2
    calc α ^ 2 = (α * r) ^ 2 / n := e
      _ ≤ kP c y ^ 2 / n := div_le_div_of_nonneg_right h1 hn0.le
      _ = (1 / √c) ^ 6 * (y ^ 2 / n) + 32 * (1 / √c) ^ 7 * (y ^ 3 / n) +
          256 * (1 / √c) ^ 8 * (y ^ 4 / n) := by unfold kP; ring
      _ ≤ (1 / √c) ^ 6 * Y + 32 * (1 / √c) ^ 7 * Y + 256 * (1 / √c) ^ 8 * Y := by gcongr
      _ = _ := by ring
  have hα1 := alpha_r_bd hn hr hαP Y1 Y2
  have hD : 0 ≤ 2 * K ^ 2 + 20 * K ^ 4 := by positivity
  have hD' : 0 ≤ 16 * K ^ 4 + (2 * K ^ 2 + 4 * K ^ 4) * exp (2 * K ^ 2 + 4 * K ^ 4) := by
    positivity
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α)]
  calc (2 * K ^ 2 + 20 * K ^ 4) * (2 * α) ^ 2 +
        (16 * K ^ 4 + (2 * K ^ 2 + 4 * K ^ 4) * exp (2 * K ^ 2 + 4 * K ^ 4)) * (2 * α) / r
      = 4 * (2 * K ^ 2 + 20 * K ^ 4) * α ^ 2 +
        2 * (16 * K ^ 4 + (2 * K ^ 2 + 4 * K ^ 4) * exp (2 * K ^ 2 + 4 * K ^ 4)) * (α / r) := by
        ring
    _ ≤ 4 * (2 * K ^ 2 + 20 * K ^ 4) *
          (((1 / √c) ^ 6 + 32 * (1 / √c) ^ 7 + 256 * (1 / √c) ^ 8) * Y) +
        2 * (16 * K ^ 4 + (2 * K ^ 2 + 4 * K ^ 4) * exp (2 * K ^ 2 + 4 * K ^ 4)) *
          (kQ c * Y) := by gcongr
    _ = kC1 K c * Y := by unfold kC1 kD kDp; ring

/-! Named quantities: `s = sS x`, `α = kα x y`, `L = kL c y N`, `Y = kY y N`. -/
noncomputable def sS {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) : ℝ := √((∑ i, x i ^ 2) / N)
noncomputable def kα {N : ℕ} (x : Fin N ⊕ Fin N → ℝ) (y : ℝ) : ℝ :=
  Hz (y / sS x) * y / (sS x ^ 3 * √(N : ℝ))
noncomputable def kL (c y : ℝ) (N : ℕ) : ℝ := 4 * kB c * (y ^ 2 + 1) / N
noncomputable def kY (y : ℝ) (N : ℕ) : ℝ := (y ^ 3 + 1) / √(N : ℝ)

lemma kL_nonneg (c y : ℝ) (N : ℕ) (hc : 0 < c) : 0 ≤ kL c y N := by
  have := kB_pos hc; unfold kL; positivity

/-- Exponential moments of `2αη` and `2Lη²` ((4.9)-(4.10) at the parameters of (4.7)). -/
theorem mq_bd {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K c y : ℝ} (hK : 0 < K) (hc : 0 < c)
    (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) (hcS : c * N ≤ ∑ i, x i ^ 2) (hy : 0 ≤ y)
    (hyr : y ≤ √(N : ℝ)) (hv : 64 * kB c * kD K * (y ^ 2 + 1) / N ≤ 1) :
    ∑ w, exp (2 * (kα x y * etaV x w)) ≤
        (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (kC1 K c * kY y N) ∧
    ∑ w, exp (2 * (kL c y N * etaV x w ^ 2)) ≤
        (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (kC2 K c * kY y N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : 0 < √(N : ℝ) := Real.sqrt_pos.2 hn
  have hnr : (N : ℝ) = √(N : ℝ) ^ 2 := (Real.sq_sqrt hn.le).symm
  have hsc : √c ≤ sS x := Real.sqrt_le_sqrt ((le_div_iff₀ hn).2 hcS)
  obtain ⟨hα0, hαP⟩ := alpha_bd hc hsc hy hr
  obtain ⟨Y1, Y2, Y3, Y4, Y0⟩ := Ybd hn1 hy hyr
  refine ⟨?_, ?_⟩
  · have h := eta_mgf_sharp hN x hK hx hs (2 * kα x y)
    refine le_trans (le_of_eq (sum_congr rfl fun w _ => by rw [mul_assoc])) (h.trans ?_)
    gcongr
    exact c1_bd hnr hr hα0 hαP Y1 Y2 Y3 Y4
  · have hBD : 0 ≤ 64 * kB c * kD K * (exp (K ^ 2 + 1 / 2) - 1) := by
      have := kC2_nonneg hK hc; unfold kC2 at this; linarith
    have hL0 : 0 ≤ 2 * kL c y N := by have := kL_nonneg c y N hc; linarith
    have hv' : 2 * kL c y N * (8 * (2 * K ^ 2 + 20 * K ^ 4)) ≤ 1 := by
      calc 2 * kL c y N * (8 * (2 * K ^ 2 + 20 * K ^ 4)) = 64 * kB c * kD K * (y ^ 2 + 1) / N := by
            unfold kL kD; ring
        _ ≤ 1 := hv
    have h := eta_sq_lin hN x hK hx hs hL0 hv'
    refine le_trans (le_of_eq (sum_congr rfl fun w _ => by rw [mul_assoc])) (h.trans ?_)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply exp_le_exp.2
    calc 2 * kL c y N * (8 * (2 * K ^ 2 + 20 * K ^ 4) * (exp (K ^ 2 + 1 / 2) - 1))
        = 64 * kB c * kD K * (exp (K ^ 2 + 1 / 2) - 1) * (y ^ 2 / N + 1 / N) := by
          unfold kL kD; ring
      _ ≤ 64 * kB c * kD K * (exp (K ^ 2 + 1 / 2) - 1) * (kY y N + kY y N) :=
          mul_le_mul_of_nonneg_left (add_le_add Y2 Y0) hBD
      _ = kC2 K c * kY y N := by unfold kC2; ring

/-- Upper half of (4.7) over the good pairings. -/
theorem up_sum {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K c y : ℝ} (hK : 0 < K) (hc : 0 < c)
    (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) (hcS : c * N ≤ ∑ i, x i ^ 2) (hy : 0 ≤ y)
    (hyr : y ≤ √(N : ℝ)) (hv : 64 * kB c * kD K * (y ^ 2 + 1) / N ≤ 1) :
    ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
        (1 - Phi (y / √(sw2 x w))) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * (1 - Phi (y / sS x)) *
        exp ((kC1 K c + kC2 K c) / 2 * kY y N) := by
  obtain ⟨hm, hq⟩ := mq_bd hN x hK hc hx hs hcS hy hyr hv
  have hG0 : 0 < 1 - Phi (y / sS x) := one_sub_Phi_pos _
  have hR : ∀ w, c / 2 ≤ sw2 x w →
      (1 - Phi (y / √(sw2 x w))) / (1 - Phi (y / sS x)) ≤
        exp (kα x y * etaV x w + kL c y N * etaV x w ^ 2) := by
    intro w hw
    rw [div_le_iff₀ hG0, mul_comm]
    exact (ratio_bd hN x hc hcS hy w hw).1
  have h := delta_upper (etaV x) (fun w => (1 - Phi (y / √(sw2 x w))) / (1 - Phi (y / sS x)))
    (fun w => c / 2 ≤ sw2 x w) (Nat.cast_nonneg _) hR hm hq
  beta_reduce at h
  rw [← sum_div, div_le_iff₀ hG0] at h
  calc _ ≤ _ := h
    _ = _ := by
      rw [show (kC1 K c * kY y N + kC2 K c * kY y N) / 2 = (kC1 K c + kC2 K c) / 2 * kY y N by
        ring]; ring

/-- Few bad pairings (variance below `c/2`), by (4.3). -/
theorem bad_card {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K c δ : ℝ} (hK : 0 < K)
    (hc : 0 < c) (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) (hcS : c * N ≤ ∑ i, x i ^ 2)
    (hδ0 : 0 < δ) (hδ1 : δ * (16 * K ^ 2) ≤ 1) (hδ2 : δ * (2 * K ^ 2 + 4 * K ^ 4) ≤ c / 8)
    (hδN : 1 ≤ δ * N) :
    ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w)).card : ℝ) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (-(δ * (c / 4) / 2) * N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := cross_tail hN x hK hx hs (c := c / 4) (by positivity) hδ0 hδ1 (by linarith) hδN
  refine le_trans ?_ h
  refine Nat.cast_le.2 (card_le_card fun w hw => ?_)
  simp only [mem_filter, mem_univ, true_and, not_le] at hw ⊢
  rw [sw2_eq', div_lt_iff₀ hn] at hw
  linarith

/-- Lower half of (4.7) over the good pairings. -/
theorem low_sum {N : ℕ} (hN : 1 ≤ N) (x : Fin N ⊕ Fin N → ℝ) {K c y a : ℝ} (hK : 0 < K)
    (hc : 0 < c) (hx : ∀ i, |x i| ≤ K) (hs : ∑ i, x i = 0) (hcS : c * N ≤ ∑ i, x i ^ 2)
    (hy : 0 ≤ y) (hyr : y ≤ √(N : ℝ)) (hv : 64 * kB c * kD K * (y ^ 2 + 1) / N ≤ 1)
    (hbad : ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w)).card : ℝ) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (-a * N)) :
    (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * (1 - Phi (y / sS x)) *
        (exp (-(2 * (kC0 K c * kY y N)) - (kC1 K c + kC2 K c) / 2 * kY y N)
          - exp (-a * N + K ^ 2 * kP c y)) ≤
      ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
        (1 - Phi (y / √(sw2 x w))) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : 0 < √(N : ℝ) := Real.sqrt_pos.2 hn
  have hnr : (N : ℝ) = √(N : ℝ) ^ 2 := (Real.sq_sqrt hn.le).symm
  have hsc : √c ≤ sS x := Real.sqrt_le_sqrt ((le_div_iff₀ hn).2 hcS)
  obtain ⟨hα0, hαP⟩ := alpha_bd hc hsc hy hr
  obtain ⟨Y1, Y2, Y3, Y4, Y0⟩ := Ybd hn1 hy hyr
  obtain ⟨hm, hq⟩ := mq_bd hN x hK hc hx hs hcS hy hyr hv
  have hG0 : 0 < 1 - Phi (y / sS x) := one_sub_Phi_pos _
  have hR : ∀ w, c / 2 ≤ sw2 x w →
      exp (kα x y * etaV x w - kL c y N * etaV x w ^ 2) ≤
        (1 - Phi (y / √(sw2 x w))) / (1 - Phi (y / sS x)) := by
    intro w hw
    rw [le_div_iff₀ hG0, mul_comm]
    exact (ratio_bd hN x hc hcS hy w hw).2
  have hjen : (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (-(kC0 K c * kY y N)) ≤
      ∑ w, exp (kα x y * etaV x w) := by
    have hj := jensen_exp (fun w : Equiv.Perm (Fin N ⊕ Fin N) => kα x y * etaV x w)
    beta_reduce at hj
    have hmean := mean_abs_le (etaV x) hr (eta_mgf_sharp hN x hK hx hs)
    refine le_trans ?_ hj
    gcongr
    rw [← mul_sum, mul_div_assoc]
    have h1 := (abs_le.1 hmean).1
    have hα1 := alpha_r_bd hnr hr hαP Y1 Y2
    have hDD : 0 ≤ kD K + kDp K := by have := kD_pos hK; have := kDp_nonneg K; linarith
    have h2 : kα x y * ((2 * K ^ 2 + 20 * K ^ 4 + (16 * K ^ 4 + (2 * K ^ 2 + 4 * K ^ 4) *
        exp (2 * K ^ 2 + 4 * K ^ 4))) / √(N : ℝ)) ≤ kC0 K c * kY y N := by
      calc _ = (kD K + kDp K) * (kα x y / √(N : ℝ)) := by unfold kD kDp; ring
        _ ≤ (kD K + kDp K) * (kQ c * kY y N) := mul_le_mul_of_nonneg_left hα1 hDD
        _ = kC0 K c * kY y N := by unfold kC0; ring
    have hα0' : 0 ≤ kα x y := hα0
    linarith [mul_le_mul_of_nonneg_left h1 hα0']
  have hup : ∑ w, exp (kα x y * etaV x w + kL c y N * etaV x w ^ 2) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp ((kC1 K c + kC2 K c) / 2 * kY y N) := by
    have h := delta_upper (etaV x) (fun w => exp (kα x y * etaV x w + kL c y N * etaV x w ^ 2))
      (fun _ => True) (Nat.cast_nonneg _) (fun w _ => le_refl _) hm hq
    rw [filter_true_of_mem (fun _ _ => trivial)] at h
    rw [show (kC1 K c + kC2 K c) / 2 * kY y N = (kC1 K c * kY y N + kC2 K c * kY y N) / 2 by ring]
    exact h
  have hbad' : ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w),
      exp (kα x y * etaV x w - kL c y N * etaV x w ^ 2) ≤
      (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (-a * N + K ^ 2 * kP c y) := by
    have hpt : ∀ w, exp (kα x y * etaV x w - kL c y N * etaV x w ^ 2) ≤ exp (K ^ 2 * kP c y) := by
      intro w
      apply exp_le_exp.2
      have hL0 : 0 ≤ kL c y N * etaV x w ^ 2 := mul_nonneg (kL_nonneg c y N hc) (sq_nonneg _)
      have he := eta_abs_le hN x hx w
      have h1 : kα x y * etaV x w ≤ kα x y * (K ^ 2 * √(N : ℝ)) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans he) hα0
      have h2 : kα x y * (K ^ 2 * √(N : ℝ)) ≤ K ^ 2 * kP c y := by
        calc kα x y * (K ^ 2 * √(N : ℝ)) = K ^ 2 * (kα x y * √(N : ℝ)) := by ring
          _ ≤ K ^ 2 * kP c y := mul_le_mul_of_nonneg_left hαP (by positivity)
      linarith
    calc _ ≤ ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w),
          exp (K ^ 2 * kP c y) := sum_le_sum fun w _ => hpt w
      _ = ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w)).card : ℝ) *
          exp (K ^ 2 * kP c y) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * exp (-a * N) * exp (K ^ 2 * kP c y) :=
          mul_le_mul_of_nonneg_right hbad (exp_pos _).le
      _ = _ := by rw [exp_add]; ring
  have h := delta_lower (etaV x) (fun w => (1 - Phi (y / √(sw2 x w))) / (1 - Phi (y / sS x)))
    (fun w => c / 2 ≤ sw2 x w) (by exact_mod_cast Fintype.card_pos) hR hjen hup hbad'
  beta_reduce at h
  rw [← sum_div, le_div_iff₀ hG0] at h
  calc _ = _ := by ring
    _ ≤ _ := h

lemma sq_half_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 2 / 2 ≤ exp u := by
  linarith [Real.quadratic_le_exp_of_nonneg hu]

/-- Real-number core of the bad-set comparison: `e^{-an} √n ≤ G(z)` once `z² ≤ an`,
`z + 1 ≤ (q+1)√n` and `n ≥ 16(q+1)/(k a²)`, `k = e^{-1/2}(2π)^{-1/2}/2`. -/
lemma bad_vs_tail {a n q z : ℝ} (ha : 0 < a) (hn : 1 ≤ n) (hq : 0 ≤ q) (hz : 0 ≤ z)
    (hz2 : z ^ 2 ≤ a * n) (hz1 : z + 1 ≤ (q + 1) * √n)
    (hN : 16 * (q + 1) / (exp (-(1 / 2)) * (√(2 * π))⁻¹ / 2 * a ^ 2) ≤ n) :
    exp (-(a * n)) * √n ≤ 1 - Phi z := by
  set k := exp (-(1 / 2)) * (√(2 * π))⁻¹ / 2 with hk
  have hk0 : 0 < k := by rw [hk]; positivity
  have hn0 : 0 < n := by linarith
  have hr : 0 < √n := Real.sqrt_pos.2 hn0
  have hsq : √n * √n = n := Real.mul_self_sqrt hn0.le
  have hq1 : 0 < q + 1 := by linarith
  have hE : (q + 1) * n ≤ k * exp (a * n / 2) := by
    have h1 := sq_half_le_exp (by positivity : (0 : ℝ) ≤ a * n / 2)
    have h2 : 16 * (q + 1) ≤ n * (k * a ^ 2) := (div_le_iff₀ (by positivity)).1 hN
    have h3 : (q + 1) * n ≤ k * ((a * n / 2) ^ 2 / 2) := by nlinarith
    calc (q + 1) * n ≤ k * ((a * n / 2) ^ 2 / 2) := h3
      _ ≤ k * exp (a * n / 2) := mul_le_mul_of_nonneg_left h1 hk0.le
  have e1 : exp (-(a * n)) = exp (-(a * n / 2)) * exp (-(a * n / 2)) := by
    rw [← exp_add]; ring_nf
  have e2 : exp (-(a * n / 2)) * exp (a * n / 2) = 1 := by rw [← exp_add]; simp
  have hA : exp (-(a * n)) * ((q + 1) * n) ≤ k * exp (-(a * n / 2)) := by
    calc exp (-(a * n)) * ((q + 1) * n) = exp (-(a * n / 2)) * (exp (-(a * n / 2)) * ((q + 1) * n)) := by
          rw [e1]; ring
      _ ≤ exp (-(a * n / 2)) * (exp (-(a * n / 2)) * (k * exp (a * n / 2))) := by gcongr
      _ = k * exp (-(a * n / 2)) * (exp (-(a * n / 2)) * exp (a * n / 2)) := by ring
      _ = k * exp (-(a * n / 2)) := by rw [e2, mul_one]
  have hGl := G_lower hz
  have hφ : (√(2 * π))⁻¹ * exp (-(a * n / 2)) ≤ phi z := by
    unfold phi
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) (by positivity)
  have hG : k * exp (-(a * n / 2)) ≤ (1 - Phi z) * ((q + 1) * √n) := by
    have h1 : exp (-(1 / 2)) * phi z ≤ (1 - Phi z) * (2 * (z + 1)) :=
      (div_le_iff₀ (by positivity)).1 hGl
    have hG0 : 0 ≤ 1 - Phi z := (one_sub_Phi_pos z).le
    have h2 : (1 - Phi z) * (2 * (z + 1)) ≤ (1 - Phi z) * (2 * ((q + 1) * √n)) :=
      mul_le_mul_of_nonneg_left (by linarith) hG0
    have h3 : exp (-(1 / 2)) * ((√(2 * π))⁻¹ * exp (-(a * n / 2))) ≤ exp (-(1 / 2)) * phi z :=
      mul_le_mul_of_nonneg_left hφ (exp_pos _).le
    rw [hk]; linarith
  have h3 : exp (-(a * n)) * √n * ((q + 1) * √n) ≤ (1 - Phi z) * ((q + 1) * √n) := by
    calc exp (-(a * n)) * √n * ((q + 1) * √n) = exp (-(a * n)) * ((q + 1) * (√n * √n)) := by ring
      _ = exp (-(a * n)) * ((q + 1) * n) := by rw [hsq]
      _ ≤ k * exp (-(a * n / 2)) := hA
      _ ≤ _ := hG
  exact le_of_mul_le_mul_right h3 (by positivity)

/-- Real-number core of the lower bound: `b ≤ e^{-C'Y}/(2√n)` and `e^{-Y} ≤ 1 - 1/(2√n)` give
`e^{-(C'+1)Y} ≤ e^{-C'Y} - b`. -/
lemma low_core {Cp Y b n : ℝ} (hn : 1 ≤ n) (hY : 1 / √n ≤ Y)
    (hb : b * exp (Cp * Y) * (2 * √n) ≤ 1) :
    exp (-((Cp + 1) * Y)) ≤ exp (-(Cp * Y)) - b := by
  have hr1 : 1 ≤ √n := Real.one_le_sqrt.2 hn
  have hr : 0 < √n := by linarith
  set t := 1 / √n with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hr]; exact hr1
  have hb' : b ≤ exp (-(Cp * Y)) * (t / 2) := by
    have hE : exp (-(Cp * Y)) * exp (Cp * Y) = 1 := by rw [← exp_add]; simp
    have h2 : b * exp (Cp * Y) ≤ t / 2 := by
      rw [ht, div_div, le_div_iff₀ (by positivity)]
      linarith [hb]
    calc b = b * exp (Cp * Y) * exp (-(Cp * Y)) := by
          rw [mul_assoc, mul_comm (exp (Cp * Y)), hE, mul_one]
      _ ≤ t / 2 * exp (-(Cp * Y)) := mul_le_mul_of_nonneg_right h2 (exp_pos _).le
      _ = _ := by ring
  have hexp : exp (-Y) ≤ 1 - t / 2 := by
    have h1 : exp (-Y) ≤ exp (-t) := exp_le_exp.2 (by linarith)
    have h2 : exp (-t) * (1 + t) ≤ 1 := by
      have := add_one_le_exp t
      have hE : exp (-t) * exp t = 1 := by rw [← exp_add]; simp
      calc exp (-t) * (1 + t) ≤ exp (-t) * exp t :=
            mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
        _ = 1 := hE
    have h3 : 1 ≤ (1 - t / 2) * (1 + t) := by nlinarith
    have h4 : exp (-t) ≤ 1 - t / 2 := by
      have hpos : 0 < 1 + t := by linarith
      have : exp (-t) * (1 + t) ≤ (1 - t / 2) * (1 + t) := h2.trans h3
      exact le_of_mul_le_mul_right this hpos
    linarith
  have e : exp (-((Cp + 1) * Y)) = exp (-(Cp * Y)) * exp (-Y) := by rw [← exp_add]; ring_nf
  rw [e]
  have := mul_le_mul_of_nonneg_left hexp (exp_pos (-(Cp * Y))).le
  linarith

set_option maxHeartbeats 1000000 in
/-- KMT 1976 II, (4.7) for pairings: with `s = sS x` and `Y = (y³+1)/√N`,
`Σ_good G(y/s_w) = card·G(y/s)·exp(±C·Y)`, and the bad pairings number at most `card·G(y/s)/√N`. -/
theorem dperm (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∃ ε C N0 : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧ ∀ N : ℕ, 1 ≤ N → N0 ≤ N →
      ∀ x : Fin N ⊕ Fin N → ℝ, (∀ i, |x i| ≤ K) → ∑ i, x i = 0 → c * N ≤ ∑ i, x i ^ 2 →
      ∀ y : ℝ, 0 ≤ y → y ≤ ε * √(N : ℝ) →
        ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
            (1 - Phi (y / √(sw2 x w))) ≤
          (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * (1 - Phi (y / sS x)) *
            exp (C * kY y N) ∧
        ((univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => ¬ c / 2 ≤ sw2 x w)).card : ℝ) ≤
          (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * (1 - Phi (y / sS x)) / √(N : ℝ) ∧
        (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) * (1 - Phi (y / sS x)) *
            exp (-(C * kY y N)) ≤
          ∑ w ∈ univ.filter (fun w : Equiv.Perm (Fin N ⊕ Fin N) => c / 2 ≤ sw2 x w),
            (1 - Phi (y / √(sw2 x w))) := by
  have hBD : 0 < kB c * kD K := mul_pos (kB_pos hc) (kD_pos hK)
  have hc' : 0 < √c := Real.sqrt_pos.2 hc
  obtain ⟨q, hqd⟩ : ∃ q : ℝ, q = 1 / √c := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hqd]; positivity
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = min (1 / (16 * K ^ 2)) (c / (8 * (2 * K ^ 2 + 4 * K ^ 4))) :=
    ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδd]; exact lt_min (by positivity) (by positivity)
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = δ * (c / 4) / 2 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [had]; positivity
  obtain ⟨Cp, hCpd⟩ : ∃ Cp : ℝ, Cp = 2 * kC0 K c + (kC1 K c + kC2 K c) / 2 := ⟨_, rfl⟩
  have hCp0 : 0 ≤ Cp := by
    have := kC0_nonneg (c := c) hK; have := kC1_nonneg (c := c) hK; have := kC2_nonneg hK hc
    rw [hCpd]; positivity
  have hQ0 := kQ_nonneg c
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = min (min 1 (1 / (128 * (kB c * kD K))))
      (min (a / q ^ 2) (a / (2 * (K ^ 2 * kQ c + Cp + 1)))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hεd]; exact lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity) (by positivity))
  have hε1 : ε ≤ 1 := by rw [hεd]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hεB : ε ≤ 1 / (128 * (kB c * kD K)) := by
    rw [hεd]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hεa : ε ≤ a / q ^ 2 := by rw [hεd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hεC : ε ≤ a / (2 * (K ^ 2 * kQ c + Cp + 1)) := by
    rw [hεd]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, Cp + 1, max (max (128 * (kB c * kD K)) (1 / δ))
    (max (16 * (q + 1) / (exp (-(1 / 2)) * (√(2 * π))⁻¹ / 2 * a ^ 2)) (16 * exp Cp / a ^ 2)),
    hε0, hε1, by linarith, ?_⟩
  intro N hN hN0 x hx hs hcS y hy hyε
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr1 : 1 ≤ √(N : ℝ) := Real.one_le_sqrt.2 hn1
  have hr : 0 < √(N : ℝ) := by linarith
  have hsq : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hn.le
  have hrn : √(N : ℝ) ≤ N := by
    have := mul_le_mul_of_nonneg_left hr1 hr.le; linarith [hsq]
  have hN1 : 128 * (kB c * kD K) ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN0)
  have hN2 : 1 / δ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN0)
  have hN3 : 16 * (q + 1) / (exp (-(1 / 2)) * (√(2 * π))⁻¹ / 2 * a ^ 2) ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN0)
  have hN4 : 16 * exp Cp / a ^ 2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN0)
  have hyr : y ≤ √(N : ℝ) := hyε.trans (mul_le_of_le_one_left hr.le hε1)
  have hy2 : y ^ 2 ≤ ε * N := by
    have h1 : y ^ 2 ≤ (ε * √(N : ℝ)) ^ 2 := pow_le_pow_left₀ hy hyε 2
    have h2 : (ε * √(N : ℝ)) ^ 2 = ε ^ 2 * N := by rw [mul_pow, Real.sq_sqrt hn.le]
    have h3 : ε ^ 2 ≤ ε := pow_le_of_le_one hε0.le hε1 (by norm_num)
    calc y ^ 2 ≤ ε ^ 2 * N := h1.trans h2.le
      _ ≤ ε * N := mul_le_mul_of_nonneg_right h3 hn.le
  have hv : 64 * kB c * kD K * (y ^ 2 + 1) / N ≤ 1 := by
    rw [div_le_one hn]
    have h1 : ε * (128 * (kB c * kD K)) ≤ 1 := (le_div_iff₀ (by positivity)).1 hεB
    have h2 : 128 * (kB c * kD K) * y ^ 2 ≤ N := by
      calc 128 * (kB c * kD K) * y ^ 2 ≤ 128 * (kB c * kD K) * (ε * N) :=
            mul_le_mul_of_nonneg_left hy2 (by positivity)
        _ = (ε * (128 * (kB c * kD K))) * N := by ring
        _ ≤ 1 * N := mul_le_mul_of_nonneg_right h1 hn.le
        _ = N := one_mul _
    linarith
  have hsc : √c ≤ sS x := Real.sqrt_le_sqrt ((le_div_iff₀ hn).2 hcS)
  have hs0 : 0 < sS x := hc'.trans_le hsc
  have hG0 : 0 < 1 - Phi (y / sS x) := one_sub_Phi_pos _
  have hcard : (0 : ℝ) ≤ (Fintype.card (Equiv.Perm (Fin N ⊕ Fin N)) : ℝ) := Nat.cast_nonneg _
  have hYnn : 0 ≤ kY y N := by unfold kY; positivity
  -- bad pairings
  have hδ1 : δ * (16 * K ^ 2) ≤ 1 := by
    have : δ ≤ 1 / (16 * K ^ 2) := by rw [hδd]; exact min_le_left _ _
    exact (le_div_iff₀ (by positivity)).1 this
  have hδ2 : δ * (2 * K ^ 2 + 4 * K ^ 4) ≤ c / 8 := by
    have : δ ≤ c / (8 * (2 * K ^ 2 + 4 * K ^ 4)) := by rw [hδd]; exact min_le_right _ _
    have := (le_div_iff₀ (by positivity)).1 this
    linarith
  have hδN : 1 ≤ δ * N := by
    have := (div_le_iff₀ hδ0).1 hN2; linarith
  have hbad0 := bad_card hN x hK hc hx hs hcS hδ0 hδ1 hδ2 hδN
  rw [show -(δ * (c / 4) / 2) = -a by rw [had]] at hbad0
  refine ⟨?_, ?_, ?_⟩
  · -- upper
    refine (up_sum hN x hK hc hx hs hcS hy hyr hv).trans ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hcard hG0.le)
    apply exp_le_exp.2
    apply mul_le_mul_of_nonneg_right _ hYnn
    have := kC0_nonneg (c := c) hK
    rw [hCpd]; linarith
  · -- bad count
    refine hbad0.trans ?_
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hcard
    rw [le_div_iff₀ hr]
    have hz0 : 0 ≤ y / sS x := div_nonneg hy hs0.le
    have hzq : y / sS x ≤ q * y := by
      rw [hqd, div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hc' hsc) hy
    have hz2 : (y / sS x) ^ 2 ≤ a * N := by
      have h1 : (y / sS x) ^ 2 ≤ (q * y) ^ 2 := pow_le_pow_left₀ hz0 hzq 2
      have h2 : ε * q ^ 2 ≤ a := (le_div_iff₀ (by positivity)).1 hεa
      have h3 : (q * y) ^ 2 = q ^ 2 * y ^ 2 := by ring
      have h4 : q ^ 2 * y ^ 2 ≤ q ^ 2 * (ε * N) := mul_le_mul_of_nonneg_left hy2 (by positivity)
      have h5 : ε * q ^ 2 * N ≤ a * N := mul_le_mul_of_nonneg_right h2 hn.le
      linarith
    have hz1 : y / sS x + 1 ≤ (q + 1) * √(N : ℝ) := by
      have h1 : q * y ≤ q * √(N : ℝ) := mul_le_mul_of_nonneg_left hyr hq0.le
      linarith
    have hmain := bad_vs_tail ha0 hn1 hq0.le hz0 hz2 hz1 hN3
    rw [show -a * (N : ℝ) = -(a * N) by ring]
    exact hmain
  · -- lower
    refine le_trans ?_ (low_sum hN x hK hc hx hs hcS hy hyr hv hbad0)
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hcard hG0.le)
    rw [show -(2 * (kC0 K c * kY y N)) - (kC1 K c + kC2 K c) / 2 * kY y N = -(Cp * kY y N) by
      rw [hCpd]; ring]
    apply low_core hn1 (by unfold kY; exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hy 3]) hr.le)
    -- b * exp(Cp Y) * 2√N ≤ 1
    have hP : kP c y ≤ kQ c * ε * N := by
      have h1 : y ≤ ε * N := hyε.trans (mul_le_mul_of_nonneg_left hrn hε0.le)
      unfold kP kQ
      have h2 : (1 / √c) ^ 3 * y ≤ (1 / √c) ^ 3 * (ε * N) := mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : 16 * (1 / √c) ^ 4 * y ^ 2 ≤ 16 * (1 / √c) ^ 4 * (ε * N) :=
        mul_le_mul_of_nonneg_left hy2 (by positivity)
      linarith
    have hYb : kY y N ≤ ε * N + 1 := by
      unfold kY
      rw [div_le_iff₀ hr]
      have h1 : y ^ 3 ≤ ε * N * √(N : ℝ) := by
        have : y ^ 2 ≤ N := hy2.trans (mul_le_of_le_one_left hn.le hε1)
        calc y ^ 3 = y * y ^ 2 := by ring
          _ ≤ (ε * √(N : ℝ)) * N := mul_le_mul hyε this (sq_nonneg _) (by positivity)
          _ = ε * N * √(N : ℝ) := by ring
      linarith
    have hεC' : ε * (K ^ 2 * kQ c + Cp) ≤ a / 2 := by
      have := (le_div_iff₀ (by positivity)).1 hεC
      linarith
    have hexp : -a * N + K ^ 2 * kP c y + Cp * kY y N ≤ -(a * N / 2) + Cp := by
      have h1 : K ^ 2 * kP c y ≤ K ^ 2 * (kQ c * ε * N) := mul_le_mul_of_nonneg_left hP (by positivity)
      have h2 : Cp * kY y N ≤ Cp * (ε * N + 1) := mul_le_mul_of_nonneg_left hYb hCp0
      have h3 : ε * (K ^ 2 * kQ c + Cp) * N ≤ a / 2 * N := mul_le_mul_of_nonneg_right hεC' hn.le
      linarith
    have hfin : exp (-(a * N / 2) + Cp) * (2 * √(N : ℝ)) ≤ 1 := by
      have h1 := sq_half_le_exp (by positivity : (0 : ℝ) ≤ a * N / 2)
      have h2 : 16 * exp Cp ≤ N * a ^ 2 := (div_le_iff₀ (by positivity)).1 hN4
      have h3 : 2 * √(N : ℝ) * exp Cp ≤ exp (a * N / 2) := by
        have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ N / 8)
        have h5 := mul_le_mul_of_nonneg_right hrn (exp_pos Cp).le
        have : 2 * N * exp Cp ≤ (a * N / 2) ^ 2 / 2 := by linarith
        linarith
      have e : exp (-(a * N / 2) + Cp) = exp Cp * exp (-(a * N / 2)) := by rw [← exp_add]; ring_nf
      have hE : exp (-(a * N / 2)) * exp (a * N / 2) = 1 := by rw [← exp_add]; simp
      rw [e]
      calc exp Cp * exp (-(a * N / 2)) * (2 * √(N : ℝ)) =
            exp (-(a * N / 2)) * (2 * √(N : ℝ) * exp Cp) := by ring
        _ ≤ exp (-(a * N / 2)) * exp (a * N / 2) := mul_le_mul_of_nonneg_left h3 (exp_pos _).le
        _ = 1 := hE
    calc exp (-a * N + K ^ 2 * kP c y) * exp (Cp * kY y N) * (2 * √(N : ℝ))
        = exp (-a * N + K ^ 2 * kP c y + Cp * kY y N) * (2 * √(N : ℝ)) := by rw [← exp_add]
      _ ≤ exp (-(a * N / 2) + Cp) * (2 * √(N : ℝ)) :=
          mul_le_mul_of_nonneg_right (exp_le_exp.2 hexp) (by positivity)
      _ ≤ 1 := hfin

end P99bcb804

end X41_Dperm

end P99Hyps

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ (K c : ℝ),
      (0 : ℝ) < K →
        (0 : ℝ) < c →
          ∃ (ε : ℝ) (C : ℝ) (N0 : ℝ),
            (0 : ℝ) < ε ∧
              ε ≤ (1 : ℝ) ∧
                (0 : ℝ) < C ∧
                  ∀ (N : ℕ),
                    (1 : ℕ) ≤ N →
                      N0 ≤ ↑N →
                        ∀ (x : Fin N ⊕ Fin N → ℝ),
                          (∀ (i : Fin N ⊕ Fin N), |x i| ≤ K) →
                            ∑ i : Fin N ⊕ Fin N, x i = (0 : ℝ) →
                              c * ↑N ≤ ∑ i : Fin N ⊕ Fin N, x i ^ (2 : ℕ) →
                                ∀ (y : ℝ),
                                  (0 : ℝ) ≤ y →
                                    y ≤ ε * √↑N →
                                      ∑ w : Equiv.Perm (Fin N ⊕ Fin N) with
                                            c / (2 : ℝ) ≤
                                              (∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) / ↑N,
                                            ((1 : ℝ) -
                                              (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                (y /
                                                  √((∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) /
                                                      ↑N))) ≤
                                          ↑(Fintype.card (Equiv.Perm (Fin N ⊕ Fin N))) *
                                              ((1 : ℝ) -
                                                (ProbabilityTheory.cdf
                                                      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                  (y / √((∑ i : Fin N ⊕ Fin N, x i ^ (2 : ℕ)) / ↑N))) *
                                            Real.exp (C * ((y ^ (3 : ℕ) + (1 : ℝ)) / √↑N)) ∧
                                        ↑(Finset.card
                                                {w : Equiv.Perm (Fin N ⊕ Fin N) |
                                                  ¬c / (2 : ℝ) ≤
                                                      (∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) /
                                                        ↑N}) ≤
                                            ↑(Fintype.card (Equiv.Perm (Fin N ⊕ Fin N))) *
                                                ((1 : ℝ) -
                                                  (ProbabilityTheory.cdf
                                                        (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                    (y / √((∑ i : Fin N ⊕ Fin N, x i ^ (2 : ℕ)) / ↑N))) /
                                              √↑N ∧
                                          ↑(Fintype.card (Equiv.Perm (Fin N ⊕ Fin N))) *
                                                ((1 : ℝ) -
                                                  (ProbabilityTheory.cdf
                                                        (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                    (y / √((∑ i : Fin N ⊕ Fin N, x i ^ (2 : ℕ)) / ↑N))) *
                                              Real.exp (-(C * ((y ^ (3 : ℕ) + (1 : ℝ)) / √↑N))) ≤
                                            ∑ w : Equiv.Perm (Fin N ⊕ Fin N) with
                                              c / (2 : ℝ) ≤
                                                (∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) / ↑N,
                                              ((1 : ℝ) -
                                                (ProbabilityTheory.cdf
                                                      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                  (y /
                                                    √((∑ i : Fin N, (x (w (Sum.inl i)) - x (w (Sum.inr i))) ^ (2 : ℕ)) /
                                                        ↑N))) := by
  first
  | exact P99bcb804.dperm
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.dperm <;> assumption)
