-- Prove2me | solution 1 for BroughanRH.bombieri
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:40:04.966172+00:00
-- url     : https://prove2.me/submissions/0b83b191-74e6-455b-9262-8d9f5baea6bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_ConnesRZ_spectral_star_square
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv_critical
import Theorems.Thm_ConnesGreen_critical_mellin_mass_identity
import Theorems.Thm_ConnesGreen_critical_mellin_density_integrable
import Theorems.Thm_ConnesGreen_gammaBracket_le_of_abs_le
import Theorems.Thm_ConnesGreen_gammaBracket_zero_le
import Theorems.Thm_ConnesGreen_digamma_stirling_log_abs
import Theorems.Thm_ConnesGreen_prime_convolution_mass_bound
import Theorems.Thm_ConnesGreen_pole_pair_re_ge_sinh_mass
import Theorems.Thm_Weil2_exists_zeta_ordinate_ne_zero_of_expType

open Complex MeasureTheory Filter Topology

noncomputable section


open MeasureTheory FourierTransform



namespace Weil2Fourier

/-- Pointwise exponential-type bound for the integrand. -/
lemma integrand_bound (f : ℝ → ℂ) (R : ℝ) (hR : 0 < R) (hRf : ∀ x : ℝ, R ≤ ‖x‖ → f x = 0)
    (z : ℂ) (t : ℝ) : ‖f t * Complex.exp (I * z * t)‖ ≤ ‖f t‖ * Real.exp (R * ‖z‖) := by
  by_cases ht : R ≤ ‖t‖
  · rw [hRf t ht]; simp
  push Not at ht
  rw [norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hre : (I * z * (t:ℂ)).re = -(z.im * t) := by simp
  rw [hre]
  have h1 : -(z.im * t) ≤ |z.im| * |t| := by
    rw [← abs_mul]; exact neg_le_abs _
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have h3 : |t| ≤ R := by rw [← Real.norm_eq_abs]; exact ht.le
  calc -(z.im * t) ≤ |z.im| * |t| := h1
    _ ≤ ‖z‖ * R := mul_le_mul h2 h3 (abs_nonneg _) (norm_nonneg _)
    _ = R * ‖z‖ := by ring

theorem fourier_pack (f : ℝ → ℂ) (hc : Continuous f) (hs : HasCompactSupport f) :
    Differentiable ℂ (fun z : ℂ => ∫ t : ℝ, f t * Complex.exp (I * z * t)) ∧
    (∃ C A : ℝ, ∀ z : ℂ, ‖∫ t : ℝ, f t * Complex.exp (I * z * t)‖ ≤ C * Real.exp (A * ‖z‖)) ∧
    (f ≠ 0 → ∃ t0 : ℝ, (∫ t : ℝ, f t * Complex.exp (I * (t0 : ℂ) * t)) ≠ 0) := by
  obtain ⟨R, hR, hRf⟩ := hs.exists_pos_le_norm
  have hfi : Integrable (fun t => ‖f t‖) := hc.norm.integrable_of_hasCompactSupport hs.norm
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => f t * Complex.exp (I * z * t)) := by
    intro z
    apply Continuous.aestronglyMeasurable
    apply hc.mul
    apply Complex.continuous_exp.comp
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · -- differentiability
    intro z0
    have hderiv : ∀ t : ℝ, ∀ z : ℂ, HasDerivAt (fun z => f t * Complex.exp (I * z * t))
        (f t * (Complex.exp (I * z * t) * (I * 1 * t))) z := by
      intro t z
      have h1 : HasDerivAt (fun z : ℂ => I * z * t) (I * 1 * t) z :=
        ((hasDerivAt_id z).const_mul I).mul_const (t:ℂ)
      exact h1.cexp.const_mul (f t)
    have hb : ∀ t : ℝ, ∀ z ∈ Metric.ball z0 1,
        ‖f t * (Complex.exp (I * z * t) * (I * 1 * t))‖ ≤
          ‖f t‖ * (Real.exp (R * (‖z0‖ + 1)) * R) := by
      intro t z hz
      by_cases ht : R ≤ ‖t‖
      · rw [hRf t ht]; simp
      push Not at ht
      have hzn : ‖z‖ ≤ ‖z0‖ + 1 := by
        have := norm_le_norm_add_norm_sub' z z0
        rw [Metric.mem_ball, dist_eq_norm] at hz
        linarith
      have e1 := integrand_bound f R hR hRf z t
      rw [norm_mul] at e1
      rw [norm_mul, norm_mul, ← mul_assoc]
      have h3 : ‖I * 1 * (t:ℂ)‖ ≤ R := by simp; rw [← Real.norm_eq_abs]; exact ht.le
      have h4 : ‖f t‖ * ‖Complex.exp (I * z * t)‖ ≤ ‖f t‖ * Real.exp (R * (‖z0‖ + 1)) := by
        refine le_trans e1 (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzn hR.le)
      calc ‖f t‖ * ‖Complex.exp (I * z * t)‖ * ‖I * 1 * (t:ℂ)‖
          ≤ ‖f t‖ * Real.exp (R * (‖z0‖ + 1)) * R :=
            mul_le_mul h4 h3 (norm_nonneg _) (by positivity)
        _ = ‖f t‖ * (Real.exp (R * (‖z0‖ + 1)) * R) := by ring
    have hbi : Integrable (fun t => ‖f t‖ * (Real.exp (R * (‖z0‖ + 1)) * R)) := hfi.mul_const _
    have hint0 : Integrable (fun t : ℝ => f t * Complex.exp (I * z0 * t)) := by
      refine Integrable.mono' (hfi.mul_const (Real.exp (R * ‖z0‖))) (hmeas z0) ?_
      exact Filter.Eventually.of_forall (fun t => integrand_bound f R hR hRf z0 t)
    have hmeas' : AEStronglyMeasurable
        (fun t : ℝ => f t * (Complex.exp (I * z0 * t) * (I * 1 * t))) := by
      apply Continuous.aestronglyMeasurable
      apply hc.mul
      apply Continuous.mul
      · apply Complex.continuous_exp.comp; fun_prop
      · fun_prop
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun z t => f t * Complex.exp (I * z * t))
      (F' := fun z t => f t * (Complex.exp (I * z * t) * (I * 1 * t)))
      (x₀ := z0) (Metric.ball_mem_nhds z0 one_pos)
      (Filter.Eventually.of_forall (fun z => hmeas z)) hint0 hmeas'
      (Filter.Eventually.of_forall (fun t z hz => hb t z hz)) hbi
      (Filter.Eventually.of_forall (fun t z _ => hderiv t z))
    exact this.2.differentiableAt
  · -- exponential type
    refine ⟨∫ t, ‖f t‖, R, fun z => ?_⟩
    have := norm_integral_le_of_norm_le (hfi.mul_const (Real.exp (R * ‖z‖)))
      (Filter.Eventually.of_forall (fun t => integrand_bound f R hR hRf z t))
    rwa [integral_mul_const] at this
  · -- nonvanishing on the real line
    intro hne
    by_contra hall
    push Not at hall
    have hF : 𝓕 f = 0 := by
      funext w
      rw [Real.fourier_real_eq_integral_exp_smul]
      have := hall (-2 * Real.pi * w)
      rw [Pi.zero_apply, ← this]
      congr 1
      funext v
      rw [smul_eq_mul, mul_comm]
      congr 2
      push_cast
      ring
    have hinv := hc.fourierInv_fourier_eq (hc.integrable_of_hasCompactSupport hs)
      (by rw [hF]; exact integrable_zero _ _ _)
    rw [hF] at hinv
    apply hne
    rw [← hinv]
    funext v
    simp [Real.fourierInv_eq]

end Weil2Fourier

namespace Weil2Bomb

open ConnesRZ

/-- The Connes convolution is Mathlib's convolution for the multiplication pairing. -/
lemma conv_eq_convolution (f g : ℝ → ℂ) :
    conv f g = MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume := by
  funext t
  simp [conv, MeasureTheory.convolution_def]

lemma isTest_starInv {g : ℝ → ℂ} (hg : IsTest g) : IsTest (starInv g) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => g (-t)) := hg.1.comp contDiff_neg
    exact (Complex.conjCLE.contDiff.comp h1 : _)
  · have h1 : HasCompactSupport (fun t : ℝ => g (-t)) := by
      have := hg.2.comp_homeomorph (Homeomorph.neg ℝ)
      simpa [Function.comp_def] using this
    have := h1.comp_left (g := starRingEnd ℂ) (map_zero _)
    unfold starInv
    simpa [Function.comp_def] using this

lemma isTest_conv {f g : ℝ → ℂ} (hf : IsTest f) (hg : IsTest g) : IsTest (conv f g) := by
  rw [conv_eq_convolution]
  refine ⟨?_, ?_⟩
  · exact hf.2.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hf.1
      (hg.1.continuous.locallyIntegrable)
  · exact hf.2.convolution (ContinuousLinearMap.mul ℝ ℂ) hg.2

/-- The archimedean weight. -/
def wt (r : ℝ) : ℝ := (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi

/-- Real part of the archimedean term of `g * g^*`. -/
lemma archTerm_re (g : ℝ → ℂ) (hg : IsTest g) :
    (archTerm (conv g (starInv g))).re =
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖mellinHat g (1 / 2 + I * r)‖ ^ 2 * wt r := by
  unfold archTerm
  have h1 : ∀ r : ℝ, mellinHat (conv g (starInv g)) (1 / 2 + I * r) *
      ((((logDeriv Complex.Gamma (1 / 4 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ)) =
      ((‖mellinHat g (1 / 2 + I * r)‖ ^ 2 * wt r : ℝ) : ℂ) := by
    intro r
    rw [mellinHat_conv_starInv_critical g hg r]
    simp [wt, Complex.digamma]
  simp_rw [h1, integral_complex_ofReal]
  have : ((1 : ℂ) / (2 * Real.pi)) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `w(r) ≥ L` far out. -/
lemma wt_large (L : ℝ) : ∃ B : ℝ, 1 ≤ B ∧ ∀ r : ℝ, B ≤ |r| → L ≤ wt r := by
  set t : ℝ := Real.exp (|L| + Real.log Real.pi + 5) with ht
  have ht1 : 1 ≤ t := Real.one_le_exp (by
    have := Real.log_pos (by linarith [Real.pi_gt_three] : (1:ℝ) < Real.pi)
    positivity)
  refine ⟨2 * t, by linarith, fun r hr => ?_⟩
  have hmono := ConnesGreen.gammaBracket_le_of_abs_le (2 * t) r (by linarith) hr
  refine le_trans ?_ hmono
  have hs := ConnesGreen.digamma_stirling_log_abs (a := 1/4) (by norm_num) (by norm_num)
    (t := t) (by rw [abs_of_pos (by linarith)]; linarith)
  have e : ((1/4 : ℝ) : ℂ) + Complex.I * (t : ℂ) = 1 / 4 + I * ((2 * t : ℝ) : ℂ) / 2 := by
    push_cast; ring
  rw [e] at hs
  have hlog : Real.log |t| = |L| + Real.log Real.pi + 5 := by
    rw [abs_of_pos (by linarith), ht, Real.log_exp]
  rw [hlog] at hs
  have h5 : 5 / t ^ 2 ≤ 5 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have := (abs_le.mp hs).1
  have hL := le_abs_self L
  linarith


lemma isTest_deriv {g : ℝ → ℂ} (hg : IsTest g) : IsTest (deriv g) :=
  ⟨(contDiff_infty_iff_deriv.mp hg.1).2, hg.2.deriv⟩

lemma mellin_crit_eq (g : ℝ → ℂ) (r : ℝ) :
    mellinHat g (1 / 2 + I * r) = ∫ t : ℝ, g t * Complex.exp (I * (r : ℂ) * t) := by
  unfold mellinHat
  congr 1; funext t; congr 2; ring

lemma mellin_deriv {g : ℝ → ℂ} (hg : IsTest g) (r : ℝ) :
    mellinHat (deriv g) (1 / 2 + I * r) = -(I * r) * mellinHat g (1 / 2 + I * r) := by
  rw [mellin_crit_eq, mellin_crit_eq]
  set c : ℂ := I * r
  have hgd : Differentiable ℝ g := (contDiff_infty_iff_deriv.mp hg.1).1
  have hcd : Continuous (deriv g) := (isTest_deriv hg).1.continuous
  have hgc : Continuous g := hg.1.continuous
  have he : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (c * Complex.exp (c * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) (c * 1) t :=
      ((hasDerivAt_id t).ofReal_comp).const_mul c
    have := h1.cexp
    simpa [mul_comm] using this
  have hec : Continuous (fun t : ℝ => Complex.exp (c * t)) := by fun_prop
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => Complex.exp (c * t)) (u' := fun t => c * Complex.exp (c * t))
    (v := g) (v' := deriv g)
    (fun x _ => he x) (fun x _ => (hgd x).hasDerivAt)
    ((hec.mul hcd).integrable_of_hasCompactSupport (hg.2.deriv.mul_left))
    (((continuous_const.mul hec).mul hgc).integrable_of_hasCompactSupport hg.2.mul_left)
    ((hec.mul hgc).integrable_of_hasCompactSupport hg.2.mul_left)
  have e1 : (∫ t : ℝ, deriv g t * Complex.exp (c * t)) =
      ∫ t : ℝ, Complex.exp (c * t) * deriv g t := by
    congr 1; funext t; ring
  have e2 : (∫ t : ℝ, c * Complex.exp (c * t) * g t) = c * ∫ t : ℝ, g t * Complex.exp (c * t) := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [e1, hIBP, e2]
  ring

lemma integrable_rsq_G {g : ℝ → ℂ} (hg : IsTest g) :
    Integrable (fun r : ℝ => r ^ 2 * ‖mellinHat g (1 / 2 + I * r)‖ ^ 2) := by
  have h := ConnesGreen.critical_mellin_density_integrable (deriv g) (isTest_deriv hg)
  refine h.congr (Eventually.of_forall (fun r => ?_))
  show ‖mellinHat (deriv g) (1 / 2 + I * ↑r)‖ ^ 2 = r ^ 2 * ‖mellinHat g (1 / 2 + I * ↑r)‖ ^ 2
  rw [mellin_deriv hg r, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

lemma continuous_mellin_crit {g : ℝ → ℂ} (hg : IsTest g) :
    Continuous (fun r : ℝ => mellinHat g (1 / 2 + I * r)) := by
  have h := (Weil2Fourier.fourier_pack g hg.1.continuous hg.2).1
  have : (fun r : ℝ => mellinHat g (1 / 2 + I * r)) =
      (fun z : ℂ => ∫ t : ℝ, g t * Complex.exp (I * z * t)) ∘ (fun r : ℝ => (r : ℂ)) := by
    funext r; simp only [Function.comp]; rw [mellin_crit_eq]
  rw [this]
  exact h.continuous.comp Complex.continuous_ofReal

lemma continuous_wt : Continuous wt := by
  unfold wt
  apply Continuous.sub _ continuous_const
  apply Complex.continuous_re.comp
  rw [continuous_iff_continuousAt]
  intro r
  set s : ℂ := 1 / 4 + I * r / 2
  have hs : 0 < s.re := by simp [s]
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z _).differentiableWithinAt
    intro m hm
    have : z.re = -(m:ℝ) := by rw [hm]; simp
    simp only [Set.mem_setOf_eq] at hz
    have : (0:ℝ) ≤ m := m.cast_nonneg
    linarith
  have han : AnalyticAt ℂ Complex.Gamma s := hdiff.analyticAt (hopen.mem_nhds hs)
  have hcont : ContinuousAt (fun z => Complex.digamma z) s := by
    show ContinuousAt (logDeriv Complex.Gamma) s
    unfold logDeriv
    exact han.deriv.continuousAt.div han.continuousAt (Complex.Gamma_ne_zero_of_re_pos hs)
  have hin : Continuous (fun r : ℝ => (1 / 4 : ℂ) + I * r / 2) := by fun_prop
  refine ContinuousAt.comp (x := r) (g := fun z => Complex.digamma z)
    (f := fun r : ℝ => (1 / 4 : ℂ) + I * r / 2) ?_ hin.continuousAt
  exact hcont

lemma wt_bound : ∃ K : ℝ, ∀ r : ℝ, |wt r| ≤ K + r ^ 2 := by
  obtain ⟨K1, hK1⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_wt.continuousOn
  set w0 := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi
  refine ⟨|K1| + |w0| + 21, fun r => ?_⟩
  have hlow : w0 ≤ wt r := ConnesGreen.gammaBracket_zero_le r
  by_cases hr : |r| ≤ 1
  · have := hK1 r (by rw [Set.mem_Icc]; constructor <;> linarith [abs_le.mp hr])
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self K1, sq_nonneg r, abs_nonneg w0]
  push Not at hr
  have hs := ConnesGreen.digamma_stirling_log_abs (a := 1/4) (by norm_num) (by norm_num)
    (t := r / 2) (by rw [abs_div, abs_two]; linarith)
  have e : ((1/4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ) = 1 / 4 + I * (r : ℂ) / 2 := by
    push_cast; ring
  rw [e] at hs
  have hup : (Complex.digamma (1 / 4 + I * (r : ℂ) / 2)).re ≤ Real.log |r / 2| + 5 / (r / 2) ^ 2 :=
    by linarith [(abs_le.mp hs).2]
  have hlog : Real.log |r / 2| ≤ |r| := by
    have h2 : 0 < |r / 2| := by rw [abs_div, abs_two]; linarith
    have := Real.log_le_sub_one_of_pos h2
    rw [abs_div, abs_two] at this ⊢; linarith
  have h5 : 5 / (r / 2) ^ 2 ≤ 20 := by
    have hr0 : r ≠ 0 := by
      intro h; rw [h, abs_zero] at hr; linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_abs r]
  have hpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hup2 : wt r ≤ |r| + 20 := by unfold wt; linarith
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le w0, sq_nonneg r, abs_nonneg K1]
  · nlinarith [sq_abs r, abs_nonneg K1, abs_nonneg w0]

lemma integrable_G_wt {g : ℝ → ℂ} (hg : IsTest g) :
    Integrable (fun r : ℝ => ‖mellinHat g (1 / 2 + I * r)‖ ^ 2 * wt r) := by
  obtain ⟨K, hK⟩ := wt_bound
  have hG := ConnesGreen.critical_mellin_density_integrable g hg
  have hG2 := integrable_rsq_G hg
  refine Integrable.mono' ((hG.const_mul K).add hG2) ?_ (Eventually.of_forall (fun r => ?_))
  · exact (((continuous_mellin_crit hg).norm.pow 2).mul continuous_wt).aestronglyMeasurable
  · have h0 : 0 ≤ ‖mellinHat g (1 / 2 + I * r)‖ ^ 2 := by positivity
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    have := hK r
    nlinarith

/-- The unconditional low-frequency lower bound. -/
lemma lo_bound (a : ℝ) (ha : 0 < a) : ∃ B : ℝ, 0 < B ∧ ∀ f : ℝ → ℂ, IsTest f →
    tsupport f ⊆ Set.Icc (-a) a →
    (weilDistribution (conv f (starInv f))).re < ∫ x : ℝ, ‖f x‖ ^ 2 →
    Real.pi * (∫ x : ℝ, ‖f x‖ ^ 2) <
      ∫ r in Set.Ioo (-B) B, ‖mellinHat f (1 / 2 + I * r)‖ ^ 2 := by
  set T : ℝ := a + 1
  set P : ℝ := 2 * (Real.sinh T - T) + 2 * ConnesGreen.activePrimeWeight T
  set w0 : ℝ := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi
  set L : ℝ := 2 * |P| + 2 + |w0|
  obtain ⟨B, hB1, hB⟩ := wt_large L
  refine ⟨B, by linarith, fun f hf hsupp hlt => ?_⟩
  have hST : WeilDefect.ConnesNative.SupportedTest T f :=
    ⟨hf, hsupp.trans (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)⟩
  set n : ℝ := ∫ x : ℝ, ‖f x‖ ^ 2
  have hn0 : 0 ≤ n := integral_nonneg (fun x => by positivity)
  set G : ℝ → ℝ := fun r => ‖mellinHat f (1 / 2 + I * r)‖ ^ 2
  have hGi : Integrable G := ConnesGreen.critical_mellin_density_integrable f hf
  have hGn : ∫ r, G r = 2 * Real.pi * n := ConnesGreen.critical_mellin_mass_identity f hf
  have hpole := ConnesGreen.pole_pair_re_ge_sinh_mass T (by linarith) f hST
  have hprime := ConnesGreen.prime_convolution_mass_bound T f hST
  have harch := archTerm_re f hf
  have hW : (weilDistribution (conv f (starInv f))).re =
      (mellinHat (conv f (starInv f)) 0 + mellinHat (conv f (starInv f)) 1).re -
        (primeSum (conv f (starInv f))).re + (archTerm (conv f (starInv f))).re := by
    unfold weilDistribution; simp only [Complex.add_re, Complex.sub_re]
  have hpre : (primeSum (conv f (starInv f))).re ≤ ‖primeSum (conv f (starInv f))‖ :=
    Complex.re_le_norm _
  -- pointwise bound
  set lo : ℝ := ∫ r in Set.Ioo (-B) B, G r
  have hpt : ∀ r : ℝ, L * G r - (L + |w0|) * (Set.Ioo (-B) B).indicator G r ≤ G r * wt r := by
    intro r
    have hG0 : 0 ≤ G r := by positivity
    by_cases hr : r ∈ Set.Ioo (-B) B
    · rw [Set.indicator_of_mem hr]
      have h1 : w0 ≤ wt r := ConnesGreen.gammaBracket_zero_le r
      have h2 : -|w0| ≤ w0 := neg_abs_le w0
      nlinarith
    · rw [Set.indicator_of_notMem hr]
      have hrB : B ≤ |r| := by
        by_contra h
        push Not at h
        exact hr ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩
      have := hB r hrB
      nlinarith
  have hint : ∫ r, (L * G r - (L + |w0|) * (Set.Ioo (-B) B).indicator G r) ≤
      ∫ r, G r * wt r :=
    integral_mono ((hGi.const_mul L).sub ((hGi.indicator measurableSet_Ioo).const_mul _))
      (integrable_G_wt hf) hpt
  rw [integral_sub (hGi.const_mul L) ((hGi.indicator measurableSet_Ioo).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator measurableSet_Ioo, hGn] at hint
  have hpi : 0 < Real.pi := Real.pi_pos
  have hharch : (archTerm (conv f (starInv f))).re ≥
      (1 / (2 * Real.pi)) * (L * (2 * Real.pi * n) - (L + |w0|) * lo) := by
    rw [harch]
    exact mul_le_mul_of_nonneg_left hint (by positivity)
  have hP : |P| ≥ P := le_abs_self P
  have key : (1 / (2 * Real.pi)) * (L * (2 * Real.pi * n) - (L + |w0|) * lo) =
      L * n - (L + |w0|) * lo / (2 * Real.pi) := by field_simp
  rw [key] at hharch
  have hsum : n > -P * n + (L * n - (L + |w0|) * lo / (2 * Real.pi)) := by
    have : -P * n = -2 * (Real.sinh T - T) * n - 2 * ConnesGreen.activePrimeWeight T * n := by
      simp only [P]; ring
    linarith
  have hLw : 0 < L + |w0| := by positivity
  have h3 : (L + |w0|) * lo / (2 * Real.pi) > (L + |w0|) * n / 2 := by
    have : (L - P - 1) * n ≥ (L + |w0|) * n / 2 := by
      have : L - P - 1 ≥ (L + |w0|) / 2 := by simp only [L]; linarith
      nlinarith
    nlinarith
  have h4 : lo / (2 * Real.pi) > n / 2 := by
    rw [mul_div_assoc] at h3
    have := (mul_lt_mul_iff_of_pos_left hLw).mp (by linarith : (L + |w0|) * (n / 2) < (L + |w0|) * (lo / (2 * Real.pi)))
    exact this
  rw [gt_iff_lt, lt_div_iff₀ (by positivity)] at h4
  linarith

/-- Spectral side under RH: nonnegativity and the single-zero bound. -/
lemma spec (hRH : RiemannHypothesis) (f : ℝ → ℂ) (hf : IsTest f) :
    0 ≤ (weilDistribution (conv f (starInv f))).re ∧
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → 0 < analyticOrderNatAt riemannZeta ρ →
      ‖∫ t : ℝ, f t * Complex.exp (I * (ρ.im : ℂ) * t)‖ ^ 2 ≤
        (weilDistribution (conv f (starInv f))).re := by
  have hline : ∀ s : ℂ, IsCriticalZero s → s.re = 1/2 := by
    intro s hs
    apply hRH s hs.1
    · rintro ⟨n, hn⟩
      have := hs.2.1
      rw [hn] at this
      simp at this
      have : (0:ℝ) ≤ n := n.cast_nonneg
      linarith
    · intro h; have := hs.2.2; rw [h] at this; simp at this
  have hS := spectral_star_square f hf
  have hre := Complex.reCLM.hasSum hS
  simp only [Function.comp_def, Complex.reCLM_apply] at hre
  have hterm : ∀ x : {s : ℂ // IsCriticalZero s},
      ((zeroMult x.1 : ℂ) * (mellinHat f x.1 *
        (starRingEnd ℂ) (mellinHat f (1 - (starRingEnd ℂ) x.1)))).re =
        (zeroMult x.1 : ℝ) * Complex.normSq (mellinHat f x.1) := by
    intro x
    have hx := hline x.1 x.2
    have h1 : 1 - (starRingEnd ℂ) x.1 = x.1 := by
      apply Complex.ext <;> simp [hx] <;> norm_num
    rw [h1, Complex.mul_conj]
    simp
  have hnn : ∀ x : {s : ℂ // IsCriticalZero s},
      0 ≤ ((zeroMult x.1 : ℂ) * (mellinHat f x.1 *
        (starRingEnd ℂ) (mellinHat f (1 - (starRingEnd ℂ) x.1)))).re := by
    intro x
    rw [hterm x]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  refine ⟨hre.nonneg hnn, fun ρ hz hpos hord => ?_⟩
  have hρre : ρ.re = 1/2 := by
    apply hRH ρ hz
    · rintro ⟨n, hn⟩
      have : ρ.im = 0 := by rw [hn]; simp
      linarith
    · intro h; rw [h] at hpos; simp at hpos
  have hcrit : IsCriticalZero ρ := ⟨hz, by rw [hρre]; norm_num, by rw [hρre]; norm_num⟩
  have hle := le_hasSum hre ⟨ρ, hcrit⟩ (fun j _ => hnn j)
  refine le_trans ?_ hle
  rw [hterm]
  have hm : (1:ℝ) ≤ (zeroMult ρ : ℝ) := by
    unfold zeroMult; exact_mod_cast hord
  have hmel : mellinHat f ρ = ∫ t : ℝ, f t * Complex.exp (I * (ρ.im : ℂ) * t) := by
    unfold mellinHat
    congr 1
    funext t
    congr 2
    have : ρ - 1/2 = I * (ρ.im : ℂ) := by
      apply Complex.ext <;> simp [hρre]
    rw [this]
  rw [← hmel, Complex.normSq_eq_norm_sq]
  have : 0 ≤ ‖mellinHat f ρ‖ ^ 2 := by positivity
  nlinarith

lemma zero_off {f : ℝ → ℂ} {a : ℝ} (hsupp : tsupport f ⊆ Set.Icc (-a) a) (t : ℝ)
    (ht : t ∉ Set.Icc (-a) a) : f t = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => ht (hsupp h))

/-- `L¹ ≤ √(2a) · L²` on `[-a,a]`. -/
lemma l1_bound {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hc : Continuous f)
    (hsupp : tsupport f ⊆ Set.Icc (-a) a) (hn : 0 < ∫ x : ℝ, ‖f x‖ ^ 2) :
    (∫ x : ℝ, ‖f x‖) ≤ Real.sqrt (2 * a) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
  set n := ∫ x : ℝ, ‖f x‖ ^ 2
  set u := Real.sqrt n
  set v := Real.sqrt (2 * a)
  have hu : 0 < u := Real.sqrt_pos.mpr hn
  have hv : 0 < v := Real.sqrt_pos.mpr (by linarith)
  have hu2 : u ^ 2 = n := Real.sq_sqrt hn.le
  have hv2 : v ^ 2 = 2 * a := Real.sq_sqrt (by linarith)
  set l := u / v
  have hl : 0 < l := div_pos hu hv
  have hpt : ∀ t, ‖f t‖ ≤ (1 / (2 * l)) * ‖f t‖ ^ 2 + l / 2 := by
    intro t
    have h0 : 0 ≤ (‖f t‖ - l) ^ 2 := sq_nonneg _
    rw [div_mul_eq_mul_div, one_mul, ← sub_nonneg]
    have : (‖f t‖ ^ 2 / (2 * l) + l / 2 - ‖f t‖) = (‖f t‖ - l) ^ 2 / (2 * l) := by
      field_simp; ring
    rw [this]; positivity
  have e1 : (∫ x : ℝ, ‖f x‖) = ∫ x in Set.Icc (-a) a, ‖f x‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [zero_off hsupp x hx, norm_zero])).symm
  have e2 : n = ∫ x in Set.Icc (-a) a, ‖f x‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [zero_off hsupp x hx, norm_zero]; ring)).symm
  have hi2 : IntegrableOn (fun x => ‖f x‖ ^ 2) (Set.Icc (-a) a) :=
    (hc.norm.pow 2).integrableOn_Icc
  have hmono : (∫ x in Set.Icc (-a) a, ‖f x‖) ≤
      ∫ x in Set.Icc (-a) a, ((1 / (2 * l)) * ‖f x‖ ^ 2 + l / 2) :=
    setIntegral_mono hc.norm.integrableOn_Icc
      ((hi2.const_mul _).add (integrableOn_const (by simp) (by simp))) hpt
  rw [integral_add (hi2.const_mul _) (integrableOn_const (by simp) (by simp)),
    integral_const_mul, ← e2, setIntegral_const] at hmono
  simp only [Real.volume_real_Icc, smul_eq_mul] at hmono
  rw [e1]
  refine hmono.trans (le_of_eq ?_)
  rw [max_eq_left (by linarith), ← hu2]
  simp only [l]
  field_simp
  linear_combination -hv2

/-- Taylor moments. -/
def mom (f : ℝ → ℂ) (j : ℕ) : ℂ := ∫ t : ℝ, f t * (I * t) ^ j / (j.factorial : ℂ)

lemma mom_bound {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hc : Continuous f)
    (hsupp : tsupport f ⊆ Set.Icc (-a) a) (j : ℕ) :
    ‖mom f j‖ ≤ (∫ x : ℝ, ‖f x‖) * (a ^ j / j.factorial) := by
  have hs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport f).trans hsupp)
  have hfi : Integrable (fun t => ‖f t‖) := hc.norm.integrable_of_hasCompactSupport hs.norm
  rw [← integral_mul_const]
  unfold mom
  refine norm_integral_le_of_norm_le (hfi.mul_const _) (Eventually.of_forall (fun t => ?_))
  by_cases ht : t ∈ Set.Icc (-a) a
  · rw [mul_div_assoc, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_natCast, Real.norm_eq_abs]
    gcongr
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  · rw [zero_off hsupp t ht]; simp

lemma phi_hasSum {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hc : Continuous f)
    (hsupp : tsupport f ⊆ Set.Icc (-a) a) (z : ℂ) :
    HasSum (fun j => mom f j * z ^ j) (∫ t : ℝ, f t * Complex.exp (I * z * t)) := by
  have hs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport f).trans hsupp)
  set F : ℕ → ℝ → ℂ := fun j t => f t * (I * z * t) ^ j / (j.factorial : ℂ)
  have hFi : ∀ j, Integrable (F j) := by
    intro j
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    have : F j = fun t => f t * ((I * z * t) ^ j / (j.factorial : ℂ)) := by
      funext t; simp only [F]; ring
    rw [this]; exact hs.mul_right
  have hfi : Integrable (fun t => ‖f t‖) := hc.norm.integrable_of_hasCompactSupport hs.norm
  have hFb : ∀ j, (∫ t, ‖F j t‖) ≤ (∫ t, ‖f t‖) * ((a * ‖z‖) ^ j / j.factorial) := by
    intro j
    rw [← integral_mul_const]
    refine integral_mono (hFi j).norm (hfi.mul_const _) (fun t => ?_)
    by_cases ht : t ∈ Set.Icc (-a) a
    · simp only [F]
      rw [mul_div_assoc, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_div, norm_pow, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_natCast, Real.norm_eq_abs]
      rw [mul_comm a]
      gcongr
      exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    · simp only [F]; rw [zero_off hsupp t ht]; simp
  have hsum : Summable (fun j => ∫ t, ‖F j t‖) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (fun t => norm_nonneg _)) hFb
      ((Real.summable_pow_div_factorial _).mul_left _)
  have h := hasSum_integral_of_summable_integral_norm hFi hsum
  have e1 : ∀ t : ℝ, ∑' j, F j t = f t * Complex.exp (I * z * t) := by
    intro t
    have := (NormedSpace.expSeries_div_hasSum_exp (I * z * t)).mul_left (f t)
    rw [← Complex.exp_eq_exp_ℂ] at this
    simp only [F, mul_div_assoc]
    exact this.tsum_eq
  have e2 : ∀ j, (∫ t, F j t) = mom f j * z ^ j := by
    intro j
    unfold mom
    rw [← integral_mul_const]
    congr 1; funext t; simp only [F]; ring
  simp only [e1, e2] at h
  exact h

lemma term_le {c : ℂ} {D a : ℝ} (ha : 0 ≤ a) {j : ℕ} (hc : ‖c‖ ≤ D * (a ^ j / j.factorial))
    (z : ℂ) : ‖c * z ^ j‖ ≤ D * ((a * ‖z‖) ^ j / j.factorial) := by
  rw [norm_mul, norm_pow]
  calc ‖c‖ * ‖z‖ ^ j ≤ D * (a ^ j / j.factorial) * ‖z‖ ^ j :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = D * ((a * ‖z‖) ^ j / j.factorial) := by rw [mul_pow]; ring

lemma exp_hasSum (D x : ℝ) :
    HasSum (fun j : ℕ => D * (x ^ j / j.factorial)) (D * Real.exp x) := by
  have := (NormedSpace.expSeries_div_hasSum_exp x).mul_left D
  rw [← Real.exp_eq_exp_ℝ] at this
  exact this

lemma ps_pack (c : ℕ → ℂ) (D a : ℝ) (ha : 0 ≤ a)
    (hc : ∀ j, ‖c j‖ ≤ D * (a ^ j / j.factorial)) :
    (∀ z : ℂ, ‖∑' j, c j * z ^ j‖ ≤ D * Real.exp (a * ‖z‖)) ∧
    Differentiable ℂ (fun z : ℂ => ∑' j, c j * z ^ j) := by
  refine ⟨fun z => tsum_of_norm_bounded (exp_hasSum D (a * ‖z‖)) (fun j => term_le ha (hc j) z),
    fun z0 => ?_⟩
  set R := ‖z0‖ + 1
  have hd : DifferentiableOn ℂ (fun z : ℂ => ∑' j, c j * z ^ j) (Metric.ball 0 R) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun j => D * ((a * R) ^ j / j.factorial))
      (exp_hasSum D (a * R)).summable (fun j => ?_) Metric.isOpen_ball (fun j w hw => ?_)
    · exact (differentiable_const _ |>.mul (differentiable_pow j)).differentiableOn
    · refine (term_le ha (hc j) w).trans ?_
      have hw' : ‖w‖ ≤ R := by
        rw [Metric.mem_ball, dist_zero_right] at hw; exact hw.le
      have hD : 0 ≤ D := le_trans (norm_nonneg _) ((hc 0).trans (by simp))
      gcongr
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))

/-- Bombieri's lower bound, conditional on RH. -/
theorem bombieri_of_RH (hRH : RiemannHypothesis) :
    ∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧
      ∀ f : ℝ → ℂ, IsTest f → tsupport f ⊆ Set.Icc (-a) a →
        c * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (weilDistribution (conv f (starInv f))).re := by
  intro a ha
  obtain ⟨B, hB, hlo⟩ := lo_bound a ha
  by_contra hcon
  push Not at hcon
  have hex : ∀ k : ℕ, ∃ f : ℝ → ℂ, IsTest f ∧ tsupport f ⊆ Set.Icc (-a) a ∧
      (weilDistribution (conv f (starInv f))).re < (1 / ((k : ℝ) + 1)) * ∫ x, ‖f x‖ ^ 2 :=
    fun k => hcon _ (by positivity)
  choose F hFt hFs hFw using hex
  set n : ℕ → ℝ := fun k => ∫ x, ‖F k x‖ ^ 2 with hn_def
  have hk1 : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) ∧ 1 / ((k : ℝ) + 1) ≤ 1 := by
    intro k
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hn : ∀ k, 0 < n k := by
    intro k
    have h0 := (spec hRH (F k) (hFt k)).1
    have h1 := hFw k
    by_contra h
    push Not at h
    have : (1 / ((k : ℝ) + 1)) * n k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hk1 k).1.le h
    simp only [n] at this
    linarith
  have hWn : ∀ k, (weilDistribution (conv (F k) (starInv (F k)))).re < n k := by
    intro k
    have h1 := hFw k
    have : (1 / ((k : ℝ) + 1)) * n k ≤ n k := by
      have := (hk1 k).2; have := hn k; nlinarith
    simp only [n] at this
    linarith
  have hlok : ∀ k, Real.pi * n k <
      ∫ r in Set.Ioo (-B) B, ‖mellinHat (F k) (1 / 2 + I * r)‖ ^ 2 :=
    fun k => hlo (F k) (hFt k) (hFs k) (hWn k)
  set D := Real.sqrt (2 * a)
  set N : ℕ → ℂ := fun k => (((Real.sqrt (n k))⁻¹ : ℝ) : ℂ)
  set M : ℕ → ℕ → ℂ := fun k j => N k * mom (F k) j
  have hNn : ∀ k, ‖N k‖ = (Real.sqrt (n k))⁻¹ := by
    intro k
    simp only [N]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hM : ∀ k j, ‖M k j‖ ≤ D * (a ^ j / j.factorial) := by
    intro k j
    simp only [M]
    rw [norm_mul, hNn]
    have h1 := mom_bound ha (hFt k).1.continuous (hFs k) j
    have h2 := l1_bound ha (hFt k).1.continuous (hFs k) (hn k)
    have hs : 0 < Real.sqrt (n k) := Real.sqrt_pos.mpr (hn k)
    have hq : 0 ≤ a ^ j / (j.factorial : ℝ) := by positivity
    calc (Real.sqrt (n k))⁻¹ * ‖mom (F k) j‖
        ≤ (Real.sqrt (n k))⁻¹ * ((D * Real.sqrt (n k)) * (a ^ j / j.factorial)) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_right h2 hq)
      _ = D * (a ^ j / j.factorial) := by field_simp
  set S : Set (ℕ → ℂ) := Set.pi Set.univ (fun j => Metric.closedBall (0 : ℂ) (D * (a ^ j / j.factorial)))
  have hS : IsCompact S := isCompact_univ_pi (fun j => isCompact_closedBall _ _)
  obtain ⟨Minf, hMinfS, φ, hφ, hlim⟩ := hS.tendsto_subseq (x := M) (fun k => by
    simp only [S, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    exact hM k)
  have hcoord : ∀ j, Tendsto (fun k => M (φ k) j) atTop (𝓝 (Minf j)) :=
    fun j => tendsto_pi_nhds.mp hlim j
  have hMinf : ∀ j, ‖Minf j‖ ≤ D * (a ^ j / j.factorial) := by
    intro j
    have := hMinfS j (Set.mem_univ _)
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  set Φ : ℂ → ℂ := fun z => ∑' j, Minf j * z ^ j
  obtain ⟨hΦb, hΦd⟩ := ps_pack Minf D a ha.le hMinf
  set Φk : ℕ → ℂ → ℂ := fun k z => N k * ∫ t : ℝ, F k t * Complex.exp (I * z * t)
  have hΦk_sum : ∀ k z, HasSum (fun j => M k j * z ^ j) (Φk k z) := by
    intro k z
    have := (phi_hasSum ha (hFt k).1.continuous (hFs k) z).mul_left (N k)
    have e : (fun j => M k j * z ^ j) = fun j => N k * (mom (F k) j * z ^ j) :=
      funext fun j => by simp only [M]; ring
    rw [e]
    exact this
  have hΦk_b : ∀ k z, ‖Φk k z‖ ≤ D * Real.exp (a * ‖z‖) := by
    intro k z
    rw [← (hΦk_sum k z).tsum_eq]
    exact (ps_pack (M k) D a ha.le (hM k)).1 z
  have hconv : ∀ z, Tendsto (fun k => Φk (φ k) z) atTop (𝓝 (Φ z)) := by
    intro z
    have : (fun k => Φk (φ k) z) = fun k => ∑' j, M (φ k) j * z ^ j :=
      funext fun k => (hΦk_sum (φ k) z).tsum_eq.symm
    rw [this]
    exact tendsto_tsum_of_dominated_convergence
      (bound := fun j => D * ((a * ‖z‖) ^ j / j.factorial)) (exp_hasSum D (a * ‖z‖)).summable
      (fun j => (hcoord j).mul_const _)
      (Eventually.of_forall fun k j => term_le ha.le (hM (φ k) j) z)
  have hzero : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im →
      0 < analyticOrderNatAt riemannZeta ρ → Φ (ρ.im : ℂ) = 0 := by
    intro ρ hz hpos hord
    have hk : ∀ k, ‖Φk k (ρ.im : ℂ)‖ ^ 2 < 1 / ((k : ℝ) + 1) := by
      intro k
      have h1 := (spec hRH (F k) (hFt k)).2 ρ hz hpos hord
      have h2 := hFw k
      simp only [Φk]
      rw [norm_mul, mul_pow, hNn, inv_pow, Real.sq_sqrt (hn k).le, inv_mul_lt_iff₀ (hn k)]
      simp only [n] at h2 ⊢
      linarith
    have hsq : Tendsto (fun k => ‖Φk (φ k) (ρ.im : ℂ)‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => by positivity) (fun k => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 := hk (φ k)
      have hφk : (k : ℝ) ≤ φ k := by exact_mod_cast hφ.id_le k
      calc _ ≤ 1 / ((φ k : ℝ) + 1) := h1.le
        _ ≤ 1 / ((k : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have hsq2 : Tendsto (fun k => ‖Φk (φ k) (ρ.im : ℂ)‖ ^ 2) atTop (𝓝 (‖Φ (ρ.im : ℂ)‖ ^ 2)) :=
      ((hconv _).norm).pow 2
    have := tendsto_nhds_unique hsq2 hsq
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  have hreal : ∀ t : ℝ, Φ (t : ℂ) = 0 := by
    intro t
    by_contra h
    obtain ⟨ρ, hz, hpos, hord, hne⟩ :=
      Weil2.exists_zeta_ordinate_ne_zero_of_expType hRH Φ hΦd D a hΦb t h
    exact hne (hzero ρ hz hpos hord)
  have hval : ∀ k, (∫ r in Set.Ioo (-B) B, ‖mellinHat (F k) (1 / 2 + I * r)‖ ^ 2) / n k =
      ∫ r in Set.Ioo (-B) B, ‖Φk k (r : ℂ)‖ ^ 2 := by
    intro k
    rw [← integral_div]
    congr 1; funext r
    simp only [Φk]
    rw [mellin_crit_eq, norm_mul, mul_pow, hNn, inv_pow, Real.sq_sqrt (hn k).le]
    simp only [n]
    ring
  have hge : ∀ k, Real.pi ≤ ∫ r in Set.Ioo (-B) B, ‖Φk k (r : ℂ)‖ ^ 2 := by
    intro k
    rw [← hval, le_div_iff₀ (hn k)]
    exact (hlok k).le
  have hcontk : ∀ k, Continuous (fun r : ℝ => Φk k (r : ℂ)) := by
    intro k
    have := (Weil2Fourier.fourier_pack (F k) (hFt k).1.continuous (hFt k).2).1
    exact continuous_const.mul (this.continuous.comp Complex.continuous_ofReal)
  set C0 := (D * Real.exp (a * B)) ^ 2
  have htend : Tendsto (fun k => ∫ r in Set.Ioo (-B) B, ‖Φk (φ k) (r : ℂ)‖ ^ 2) atTop
      (𝓝 (∫ r in Set.Ioo (-B) B, ‖Φ (r : ℂ)‖ ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C0)
      (fun k => ((hcontk (φ k)).norm.pow 2).aestronglyMeasurable)
      (integrableOn_const (by simp) (by simp)) (fun k => ?_)
      (Eventually.of_forall fun r => ((hconv r).norm).pow 2)
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall (fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := hΦk_b (φ k) r
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have h2 : D * Real.exp (a * ‖(r : ℂ)‖) ≤ D * Real.exp (a * B) := by
      gcongr
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨hr.1.le, hr.2.le⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
  have hzeroInt : (∫ r in Set.Ioo (-B) B, ‖Φ (r : ℂ)‖ ^ 2) = 0 := by
    simp [hreal]
  rw [hzeroInt] at htend
  have := ge_of_tendsto' htend (fun k => hge (φ k))
  linarith [Real.pi_pos]

end Weil2Bomb

theorem solution :
    ∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧
      ∀ f : ℝ → ℂ, ConnesRZ.IsTest f → tsupport f ⊆ Set.Icc (-a) a →
        c * (∫ x : ℝ, ‖f x‖^2) ≤
          (ConnesRZ.weilDistribution (ConnesRZ.conv f (ConnesRZ.starInv f))).re :=
  Weil2Bomb.bombieri_of_RH riemann_hypothesis
