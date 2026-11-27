-- Prove2me | solution 1 for GRH.nonnegative_mellin_logarithmic_derivative_excludes_zeros
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:46:35.732285+00:00
-- url     : https://prove2.me/submissions/e46825b1-4b69-41f1-8f4b-825881a1b67d

import Theorems.Thm_GRH_nonnegative_mellin_continuation_from_real_axis
import Theorems.Thm_GRH_positive_residue_of_logarithmic_derivative_at_a_zero
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp

open Complex MeasureTheory Filter Set Topology GRH.OneSidedMoebius

private theorem transform_nonneg {A : ℝ → ℝ} (h0 : ∀ x, 1<x → 0≤A x) (t : ℝ) :
    0 ≤ (transform A (t:ℂ)).re := by
  have h : transform A (t:ℂ) = ((∫ x in Ioi 1, A x * x^(-t-1)) : ℝ) := by
    unfold transform
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
    simp only [Complex.ofReal_mul,Complex.ofReal_cpow hx0,Complex.ofReal_sub,
      Complex.ofReal_neg,Complex.ofReal_one]
  rw [h, Complex.ofReal_re]
  exact setIntegral_nonneg measurableSet_Ioi fun x hx => mul_nonneg (h0 x hx)
    (Real.rpow_nonneg (zero_lt_one.trans hx).le _)

private theorem ode {A : ℝ → ℝ} {P : ℂ → ℂ} {D θ b : ℝ}
    (hP : Differentiable ℂ P) (hr : ∀ z : ℂ, 1 < z.re → P z ≠ 0)
    (hθ : 0<θ) (hb : θ≤b) (hb1 : b≤1)
    (hm : Measurable A) (h0 : ∀ x, 1<x → 0≤A x)
    (hi : ∀ σ : ℝ, 1<σ → IntegrableOn (fun x : ℝ => A x*x^(-σ-1)) (Ioi 1))
    (hreal : ∀ t : ℝ, b<t → P (t:ℂ) ≠ 0)
    (hf : ∀ z : ℂ, 1<z.re → transform A z = (D:ℂ)/(z-θ)-(logDeriv P z+1)/z) :
    DifferentiableOn ℂ (transform A) {z : ℂ | b<z.re} ∧
    ∀ z : ℂ, b<z.re → deriv P z = (z*((D:ℂ)/(z-θ)-transform A z)-1)*P z := by
  let U : Set ℂ := {z | θ<z.re} ∩ {z | P z ≠ 0}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_compl_singleton.preimage hP.continuous)
  have z0 (z : ℂ) (hz : θ<z.re) : z ≠ 0 := by intro e; simp [e] at hz; linarith
  have zθ (z : ℂ) (hz : θ<z.re) : z-(θ:ℂ) ≠ 0 :=
    sub_ne_zero.mpr fun e => by simp [e] at hz
  let G := fun z : ℂ => (D:ℂ)/(z-θ)-(logDeriv P z+1)/z
  have hG : DifferentiableOn ℂ G U := by
    rintro z ⟨hz,hp⟩
    have hd : DifferentiableAt ℂ (logDeriv P) z := (hP.deriv z).div (hP z) hp
    exact (((differentiableAt_const (D:ℂ)).div (differentiableAt_id.sub_const (θ:ℂ)) (zθ z hz)).sub
      ((hd.add_const 1).div differentiableAt_id (z0 z hz))).differentiableWithinAt
  have hF := GRH.nonnegative_mellin_continuation_from_real_axis A hm h0 hi hU hG
    (fun z hz => ⟨lt_of_le_of_lt (hb.trans hb1) hz,hr z hz⟩)
    (fun t ht => ⟨lt_of_le_of_lt hb ht,hreal t ht⟩) hf
  refine ⟨hF,?_⟩
  let V : Set ℂ := {z | b<z.re}
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  let H := fun z : ℂ => (z*((D:ℂ)/(z-θ)-transform A z)-1)*P z
  have hquot : DifferentiableOn ℂ (fun z : ℂ => (D:ℂ)/(z-θ)) V :=
    (differentiableOn_const (c:=(D:ℂ))).div (differentiableOn_id.sub_const (θ:ℂ))
      (fun z hz => zθ z (hb.trans_lt hz))
  have hH : DifferentiableOn ℂ H V :=
    ((differentiableOn_id.mul (hquot.sub hF)).sub_const 1).mul hP.differentiableOn
  have h2 : (2:ℂ) ∈ V := by change b < (2:ℂ).re; norm_num; linarith
  have eqq : EqOn (deriv P) H V := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hP.deriv.differentiableOn.analyticOnNhd hV) (hH.analyticOnNhd hV)
      (convex_halfSpace_re_gt b).isPreconnected h2
    have hn : {s : ℂ | 1 < s.re} ∈ 𝓝 (2:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    have hz0 := z0 z ((hb.trans hb1).trans_lt hz)
    have hp := hr z hz
    dsimp only [H]
    rw [hf z hz,logDeriv_apply]
    field_simp
    ring
  exact fun z hz => eqq hz

theorem solution (P : ℂ → ℂ) (A : ℝ → ℝ) (D θ : ℝ)
    (hP : Differentiable ℂ P) (hr : ∀ z : ℂ, 1 < z.re → P z ≠ 0)
    (hθ : 0<θ) (hθ1 : θ<1) (hm : Measurable A) (h0 : ∀ x, 1<x → 0≤A x)
    (hi : ∀ σ : ℝ, 1<σ → IntegrableOn (fun x : ℝ => A x*x^(-σ-1)) (Ioi 1))
    (hf : ∀ z : ℂ, 1<z.re → transform A z = (D:ℂ)/(z-θ)-(logDeriv P z+1)/z) :
    ∀ z : ℂ, θ<z.re → P z ≠ 0 := by
  have hP0 : P ≠ 0 := fun e => hr 2 (by norm_num) (by simp [e])
  have reals (a : ℝ) (ha : θ<a) : P (a:ℂ) ≠ 0 := by
    intro ha0
    have ha1 : a ≤ 1 := le_of_not_gt fun h => hr a h ha0
    let K : Set ℝ := Icc a 1 ∩ {u | P (u:ℂ)=0}
    have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_eq (hP.continuous.comp
      Complex.continuous_ofReal) continuous_const)
    have hne : K.Nonempty := ⟨a,⟨⟨le_rfl,ha1⟩,ha0⟩⟩
    obtain ⟨b,hb,hmax⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
    have hbθ := ha.trans_le hb.1.1
    have hreal (t : ℝ) (ht : b<t) : P (t:ℂ) ≠ 0 := by
      intro e
      by_cases h : t≤1
      · exact ht.not_ge (hmax (show t ∈ K from ⟨⟨hb.1.1.trans ht.le,h⟩,e⟩))
      · exact hr t (lt_of_not_ge h) e
    obtain ⟨_,ho⟩ := ode hP hr hθ hbθ.le hb.1.2 hm h0 hi hreal hf
    obtain ⟨m,hpos,_,hl⟩ := GRH.positive_residue_of_logarithmic_derivative_at_a_zero
      P hP hP0 b hb.2
    have hc : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] b) (𝓝[≠] (b:ℂ)) :=
      Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun x hx =>
        show (x:ℂ) ≠ (b:ℂ) from Complex.ofReal_injective.ne (ne_of_gt hx))
    have hmLim := Complex.continuous_re.continuousAt.tendsto.comp (hl.comp hc)
    have hright : Tendsto (fun t : ℝ => (t-b)*(t*(D/(t-θ))-1)) (𝓝[>] b) (𝓝 0) := by
      have h : ContinuousAt (fun t : ℝ => (t-b)*(t*(D/(t-θ))-1)) b := by fun_prop (disch := linarith)
      simpa using h.continuousWithinAt.tendsto (s:=Ioi b)
    have hle : ∀ᶠ (t : ℝ) in 𝓝[>] b, (((t:ℂ)-(b:ℂ))*logDeriv P (t:ℂ)).re ≤
        (t-b)*(t*(D/(t-θ))-1) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : b<t := ht
      have hv := hreal t ht'
      have hlog : logDeriv P (t:ℂ) = (t:ℂ)*((D:ℂ)/(t-θ)-transform A (t:ℂ))-1 := by
        rw [logDeriv_apply,ho t ht',mul_div_cancel_right₀ _ hv]
      rw [hlog,← Complex.ofReal_sub,Complex.re_ofReal_mul]
      have hdiv : ((D:ℂ)/((t:ℂ)-(θ:ℂ))).re = D/(t-θ) := by
        rw [← ofReal_sub,← ofReal_div,ofReal_re]
      simp only [sub_re,Complex.re_ofReal_mul,one_re,hdiv]
      nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr ht'.le) (hθ.trans (hbθ.trans ht')).le)
        (transform_nonneg h0 t)]
    have contra := le_of_tendsto_of_tendsto hmLim hright hle
    change (m:ℂ).re ≤ 0 at contra
    simp at contra
    omega
  obtain ⟨hF,ho⟩ := ode hP hr hθ le_rfl hθ1.le hm h0 hi reals hf
  intro z hz hz0
  obtain ⟨m,hm',hn,hl⟩ := GRH.positive_residue_of_logarithmic_derivative_at_a_zero
    P hP hP0 z hz0
  let H := fun w : ℂ => w*((D:ℂ)/(w-θ)-transform A w)-1
  have hU : {w : ℂ | θ<w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hzc : z-(θ:ℂ) ≠ 0 := sub_ne_zero.mpr fun e => by simp [e] at hz
  have hH : ContinuousAt H z := ((continuousAt_id.mul
    ((continuousAt_const.div (continuousAt_id.sub_const _) hzc).sub
      (hF.differentiableAt hU).continuousAt)).sub_const 1)
  have lh : Tendsto (fun w : ℂ => (w-z)*H w) (𝓝[≠] z) (𝓝 0) := by
    have h : ContinuousAt (fun w : ℂ => (w-z)*H w) z := (continuousAt_id.sub_const z).mul hH
    simpa using h.continuousWithinAt.tendsto (s:={z}ᶜ)
  have heq : (fun w : ℂ => (w-z)*H w) =ᶠ[𝓝[≠] z] (fun w => (w-z)*logDeriv P w) := by
    filter_upwards [hn,nhdsWithin_le_nhds hU] with w hw hw'
    rw [logDeriv_apply,ho w hw',mul_div_cancel_right₀ _ hw]
  have h := tendsto_nhds_unique (lh.congr' heq) hl
  exact (Nat.cast_ne_zero.mpr hm'.ne' : (m:ℂ) ≠ 0) h.symm
