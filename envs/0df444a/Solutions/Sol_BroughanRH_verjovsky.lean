-- Prove2me | solution 1 for BroughanRH.verjovsky
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:38:56.628792+00:00
-- url     : https://prove2.me/submissions/2c56c05d-bd98-4ee0-87ea-d09cd3ab0e0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Zeta23_StirlingVert_re_digamma_stirling
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_le_of_re_pos
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_sub_one_le
import Theorems.Thm_Titchmarsh_inv_riemannZeta_le_rpow_of_riemannHypothesis
import Theorems.Thm_ResidueTheoremOnRectangleWithSimplePole_prime
import Theorems.Thm_riemann_hypothesis

section V1

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace VerjMellin

/-- integration by parts against `x^(s-1)` on `[α,β]` -/
lemma ibp (u u' : ℝ → ℝ) (hu : ∀ x, HasDerivAt u (u' x) x) (hu'c : Continuous u')
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hua : u α = 0) (hub : u β = 0) (s : ℂ) (hs : s ≠ 0) :
    ∫ x in α..β, (x:ℂ) ^ (s - 1) * (u x : ℂ) = -(1 / s) * ∫ x in α..β, (x:ℂ) ^ s * (u' x : ℂ) := by
  have hv : ∀ x ∈ uIcc α β, HasDerivAt (fun y : ℝ => (y : ℂ) ^ (s - 1 + 1) / (s - 1 + 1))
      ((x:ℂ) ^ (s - 1)) x := by
    intro x hx
    rw [uIcc_of_le hαβ] at hx
    exact hasDerivAt_ofReal_cpow_const' (by linarith [hx.1]) (by
      intro h; apply hs; linear_combination h)
  have hU : ∀ x ∈ uIcc α β, HasDerivAt (fun y : ℝ => (u y : ℂ)) ((u' x : ℂ)) x :=
    fun x _ => (hu x).ofReal_comp
  have hcp : ContinuousOn (fun x : ℝ => (x:ℂ) ^ (s - 1)) (uIcc α β) := by
    intro x hx
    rw [uIcc_of_le hαβ] at hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const
    simp only [ofReal_mem_slitPlane]; linarith [hx.1]
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU hv
    ((continuous_ofReal.comp hu'c).intervalIntegrable _ _) (hcp.intervalIntegrable)
  rw [show (∫ x in α..β, (x:ℂ) ^ (s - 1) * (u x : ℂ)) =
      ∫ x in α..β, (u x : ℂ) * (x:ℂ) ^ (s - 1) by
        congr 1; funext x; ring, h, hua, hub]
  simp only [ofReal_zero, zero_mul, sub_zero, zero_sub, sub_add_cancel]
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_neg]
  congr 1; funext x
  field_simp

lemma zero_out {α β : ℝ} (g : ℝ → ℝ) (hg : tsupport g ⊆ Ioo α β) {x : ℝ} (hx : x ∉ Ioo α β) :
    g =ᶠ[𝓝 x] 0 := by
  have : x ∉ tsupport g := fun h => hx (hg h)
  exact notMem_tsupport_iff_eventuallyEq.mp this

lemma tsupport_deriv_sub {α β : ℝ} (f : ℝ → ℝ) (hts : tsupport f ⊆ Ioo α β) :
    tsupport (deriv f) ⊆ Ioo α β :=
  (tsupport_deriv_subset (𝕜 := ℝ) (f := f)).trans hts

/-- Data: `f` is `C^2` with support in `[α,β] ⊂ (0,∞)`. -/
structure Good (f : ℝ → ℝ) (α β : ℝ) : Prop where
  hα : 0 < α
  hαβ : α < β
  diff : Differentiable ℝ f
  diff' : Differentiable ℝ (deriv f)
  cont'' : Continuous (deriv (deriv f))
  hts : tsupport f ⊆ Ioo α β

lemma Good.of_contDiff {f : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (hf2 : ContDiff ℝ 2 f)
    (hts : tsupport f ⊆ Ioo α β) : Good f α β := by
  have h1 := (contDiff_succ_iff_deriv (n := 1)).mp hf2
  have h2 := (contDiff_succ_iff_deriv (n := 0)).mp h1.2.2
  exact ⟨hα, hαβ, h1.1, h2.1, h2.2.2.continuous, hts⟩

lemma integrable_decay (K : ℝ) : Integrable (fun t : ℝ => K / (1 + |t|) ^ 2) := by
  have : Integrable (fun t : ℝ => (1 + |t|) ^ (-(2:ℝ))) :=
    integrable_one_add_norm (E := ℝ) (r := 2) (by simp) |>.congr (by
      filter_upwards with t; simp [Real.norm_eq_abs])
  refine (this.const_mul K).congr ?_
  filter_upwards with t
  rw [Real.rpow_neg (by positivity), Real.rpow_two, div_eq_mul_inv]

namespace Good
variable {f : ℝ → ℝ} {α β : ℝ} (G : Good f α β)
include G

lemma f_zero {x : ℝ} (hx : x ∉ Ioo α β) : f x = 0 := (zero_out f G.hts hx).eq_of_nhds

lemma df_zero {x : ℝ} (hx : x ∉ Ioo α β) : deriv f x = 0 :=
  (zero_out (deriv f) (tsupport_deriv_sub f G.hts) hx).eq_of_nhds

lemma cont : Continuous f := G.diff.continuous
lemma cont' : Continuous (deriv f) := G.diff'.continuous

lemma mellin_eq (s : ℂ) :
    mellin (fun x => (f x : ℂ)) s = ∫ x in α..β, (x:ℂ) ^ (s - 1) * (f x : ℂ) := by
  have hz : ∀ x, x ∉ Ioc α β → (x:ℂ) ^ (s - 1) * (f x : ℂ) = 0 := by
    intro x hx
    have : x ∉ Ioo α β := fun h => hx ⟨h.1, h.2.le⟩
    rw [G.f_zero this]; simp
  unfold mellin
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_of_le G.hαβ.le,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  have : x ∉ Ioo α β := fun h => hx (lt_trans G.hα h.1)
  rw [G.f_zero this]; simp

lemma mellin_eq2 (s : ℂ) (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    mellin (fun x => (f x : ℂ)) s =
      (1 / (s * (s + 1))) * ∫ x in α..β, (x:ℂ) ^ (s + 1) * ((deriv (deriv f) x : ℝ) : ℂ) := by
  rw [G.mellin_eq s]
  have hnot : α ∉ Ioo α β := fun h => lt_irrefl _ h.1
  have hnot2 : β ∉ Ioo α β := fun h => lt_irrefl _ h.2
  rw [ibp f (deriv f) (fun x => (G.diff x).hasDerivAt) G.cont' α β G.hα G.hαβ.le
    (G.f_zero hnot) (G.f_zero hnot2) s hs0]
  have h2 := ibp (deriv f) (deriv (deriv f)) (fun x => (G.diff' x).hasDerivAt) G.cont''
    α β G.hα G.hαβ.le (G.df_zero hnot) (G.df_zero hnot2) (s + 1) hs1
  rw [add_sub_cancel_right] at h2
  rw [h2]
  field_simp

/-- a uniform bound on the second-derivative integral -/
lemma exists_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 3 →
    ‖∫ x in α..β, (x:ℂ) ^ (s + 1) * ((deriv (deriv f) x : ℝ) : ℂ)‖ ≤ K := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := α) (b := β)).exists_bound_of_continuousOn
    G.cont''.continuousOn
  refine ⟨(max 1 β) ^ (4:ℝ) * |M| * (β - α), by
    have := G.hαβ; positivity, fun s hs1 hs3 => ?_⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := α) (b := β)
    (C := (max 1 β) ^ (4:ℝ) * |M|) (f := fun x => (x:ℂ) ^ (s + 1) * ((deriv (deriv f) x : ℝ) : ℂ)) ?_
  · rw [abs_of_pos (show (0:ℝ) < β - α by linarith [G.hαβ])] at h; exact h
  intro x hx
  rw [uIoc_of_le G.hαβ.le] at hx
  have hx0 : 0 < x := lt_trans G.hα hx.1
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real]
  have h1 : x ^ (s + 1).re ≤ (max 1 β) ^ (4:ℝ) := by
    simp only [add_re, one_re]
    calc x ^ (s.re + 1) ≤ (max 1 β) ^ (s.re + 1) := by
          apply Real.rpow_le_rpow hx0.le (hx.2.trans (le_max_right _ _)) (by linarith)
      _ ≤ (max 1 β) ^ (4:ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith)
  have h2 : ‖deriv (deriv f) x‖ ≤ |M| := (hM x ⟨hx.1.le, hx.2⟩).trans (le_abs_self M)
  rw [Real.norm_eq_abs] at h2
  have : 0 ≤ x ^ (s + 1).re := Real.rpow_nonneg hx0.le _
  calc x ^ (s + 1).re * |deriv (deriv f) x| ≤ (max 1 β) ^ (4:ℝ) * |M| := by
        apply mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

/-- decay of the Mellin transform -/
lemma decay : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3 →
    ‖mellin (fun x => (f x : ℂ)) s‖ ≤ K / (1 + |s.im|) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := G.exists_bound
  refine ⟨9 * K, by positivity, fun s hs1 hs3 => ?_⟩
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs1; simp at hs1; linarith
  have hs1' : s + 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  rw [G.mellin_eq2 s hs0 hs1', norm_mul]
  have hb := hK s (by linarith) hs3
  have hn1 : max (1/2) |s.im| ≤ ‖s‖ := max_le (by
      have := Complex.abs_re_le_norm s; rw [abs_of_pos (by linarith)] at this; linarith)
    (Complex.abs_im_le_norm s)
  have hn2 : max (1/2) |s.im| ≤ ‖s + 1‖ := max_le (by
      have := Complex.abs_re_le_norm (s+1); simp at this; rw [abs_of_pos (by linarith)] at this
      linarith)
    (by have := Complex.abs_im_le_norm (s+1); simpa using this)
  have hm : (1 + |s.im|) / 3 ≤ max (1/2) |s.im| := by
    rcases le_total (1/2) |s.im| with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hpos : 0 < (1 + |s.im|) / 3 := by positivity
  have hprod : ((1 + |s.im|) / 3) ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, sq]
    exact mul_le_mul (hm.trans hn1) (hm.trans hn2) hpos.le (norm_nonneg _)
  have hprod_pos : 0 < ‖s * (s + 1)‖ := lt_of_lt_of_le (by positivity) hprod
  rw [norm_div, norm_one]
  calc 1 / ‖s * (s + 1)‖ * ‖∫ x in α..β, (x:ℂ) ^ (s + 1) * ((deriv (deriv f) x : ℝ) : ℂ)‖
      ≤ 1 / ((1 + |s.im|) / 3) ^ 2 * K := by
        apply mul_le_mul _ hb (norm_nonneg _) (by positivity)
        exact one_div_le_one_div_of_le (by positivity) hprod
    _ = 9 * K / (1 + |s.im|) ^ 2 := by field_simp; ring

lemma isBigO_zero_top (a : ℝ) : (fun x => (f x : ℂ)) =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [eventually_ge_atTop β] with x hx
  have : x ∉ Ioo α β := fun h => absurd h.2 (not_lt.mpr hx)
  rw [G.f_zero this]; simp

lemma isBigO_zero_bot (b : ℝ) : (fun x => (f x : ℂ)) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  have : Iio α ∈ 𝓝[>] (0:ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds G.hα)
  filter_upwards [this] with x hx
  have : x ∉ Ioo α β := fun h => absurd h.1 (not_lt.mpr (le_of_lt hx))
  rw [G.f_zero this]; simp

lemma locInt : LocallyIntegrableOn (fun x => (f x : ℂ)) (Ioi 0) :=
  (continuous_ofReal.comp G.cont).locallyIntegrable.locallyIntegrableOn _

lemma convergent (s : ℂ) : MellinConvergent (fun x => (f x : ℂ)) s :=
  mellinConvergent_of_isBigO_rpow G.locInt (G.isBigO_zero_top (s.re + 1)) (by linarith)
    (G.isBigO_zero_bot (s.re - 1)) (by linarith)

lemma differentiable : Differentiable ℂ (mellin (fun x => (f x : ℂ))) := fun s =>
  mellin_differentiableAt_of_isBigO_rpow G.locInt (G.isBigO_zero_top (s.re + 1)) (by linarith)
    (G.isBigO_zero_bot (s.re - 1)) (by linarith)

lemma verticalIntegrable (σ : ℝ) (h1 : 1/2 ≤ σ) (h3 : σ ≤ 3) :
    VerticalIntegrable (mellin (fun x => (f x : ℂ))) σ := by
  obtain ⟨K, hK0, hK⟩ := G.decay
  unfold VerticalIntegrable
  refine Integrable.mono' (integrable_decay K) ?_ ?_
  · exact (G.differentiable.continuous.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with t
    have := hK (σ + t * I) (by simp; linarith) (by simp; linarith)
    simpa using this

lemma inversion (x : ℝ) (hx : 0 < x) :
    mellinInv 3 (mellin (fun x => (f x : ℂ))) x = (f x : ℂ) :=
  mellinInv_mellin_eq 3 _ hx (G.convergent _) (G.verticalIntegrable 3 (by norm_num) le_rfl)
    (continuous_ofReal.comp G.cont).continuousAt

lemma mellin_two : mellin (fun x => (f x : ℂ)) 2 = ((∫ x in Ioi (0:ℝ), x * f x : ℝ) : ℂ) := by
  unfold mellin
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul]
  norm_num

end Good

end VerjMellin
end V1

section V2

open Complex Set Filter Topology
open scoped Real

namespace VerjZeta

lemma line_ne (y u : ℝ) (hu : 0 < u) : ∀ m : ℕ, ((u : ℂ) + I * y) ≠ -m := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := m.cast_nonneg
  linarith

lemma gamma_hasDerivAt_line (y u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => Complex.Gamma ((v : ℂ) + I * y))
      (deriv Complex.Gamma ((u : ℂ) + I * y)) u := by
  have hG := (Complex.differentiableAt_Gamma _ (line_ne y u hu)).hasDerivAt
  have hl : HasDerivAt (fun w : ℂ => w + I * y) 1 (u : ℂ) := (hasDerivAt_id _).add_const _
  have h2 := (hG.comp (u : ℂ) hl).comp_ofReal
  rw [mul_one] at h2
  exact h2

lemma gamma_line_ne (y u : ℝ) (hu : 0 < u) : Complex.Gamma ((u : ℂ) + I * y) ≠ 0 :=
  Complex.Gamma_ne_zero (line_ne y u hu)

lemma log_normSq_gamma_hasDerivAt (y u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => Real.log (‖Complex.Gamma ((v : ℂ) + I * y)‖ ^ 2))
      (2 * (Complex.digamma ((u : ℂ) + I * y)).re) u := by
  set z := ((u : ℂ) + I * y)
  have hne := gamma_line_ne y u hu
  have h1 := (gamma_hasDerivAt_line y u hu).norm_sq
  have hpos : (‖Complex.Gamma z‖ ^ 2) ≠ 0 := by positivity
  have h2 := h1.log hpos
  convert h2 using 1
  rw [Complex.inner, Complex.digamma_def, logDeriv_apply]
  set G := Complex.Gamma z
  set D := deriv Complex.Gamma z
  have hG : G ≠ 0 := hne
  have hc : (starRingEnd ℂ) G ≠ 0 := by simpa using hG
  have : D / G = D * (starRingEnd ℂ) G / ((Complex.normSq G : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    field_simp
  rw [this, Complex.div_ofReal_re, Complex.normSq_eq_norm_sq]; ring

lemma digamma_near_log (c b : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hb : 1 ≤ |b|) :
    abs ((Complex.digamma ((c : ℂ) + I * b)).re - Real.log |b|) ≤ 5 := by
  have hst := Zeta23.StirlingVert.re_digamma_stirling (a := c) hc0 hc1 (t := b) (by linarith)
  have hb2 : (4:ℝ) / b ^ 2 ≤ 4 := by
    have : (1:ℝ) ≤ b ^ 2 := by have := sq_abs b; nlinarith
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hbpos : 0 < |b| := by linarith
  have hl1 : Real.log |b| ≤ (1/2) * Real.log (c ^ 2 + b ^ 2) := by
    have : |b| ^ 2 ≤ c ^ 2 + b ^ 2 := by rw [sq_abs]; nlinarith
    have := Real.log_le_log (by positivity) this
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hl2 : (1/2) * Real.log (c ^ 2 + b ^ 2) ≤ Real.log |b| + 1 := by
    have : c ^ 2 + b ^ 2 ≤ |b| ^ 2 * Real.exp 1 ^ 2 := by
      rw [sq_abs]
      have he : (2:ℝ) ≤ Real.exp 1 ^ 2 := by
        have := Real.add_one_le_exp 1; nlinarith
      have : (1:ℝ) ≤ b ^ 2 := by have := sq_abs b; nlinarith
      nlinarith
    have := Real.log_le_log (by positivity) this
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_exp] at this
    push_cast at this; linarith
  rw [abs_le] at hst ⊢
  constructor <;> linarith [hst.1, hst.2]

lemma gamma_ratio (a b : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (hb : 1 ≤ |b|) :
    ‖Complex.Gamma ((a : ℂ) + I * b)‖ ≤
      Real.exp (5/2) * |b| ^ (a - 1/2) * ‖Complex.Gamma (((1/2 : ℝ) : ℂ) + I * b)‖ := by
  set g := fun v : ℝ => Real.log (‖Complex.Gamma ((v : ℂ) + I * b)‖ ^ 2) with hg
  have hderiv : ∀ v : ℝ, 0 < v → HasDerivAt g (2 * (Complex.digamma ((v : ℂ) + I * b)).re) v :=
    fun v hv => log_normSq_gamma_hasDerivAt b v hv
  -- mean value theorem between a and 1/2
  have key : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ g a - g (1/2) = 2 * (Complex.digamma ((c : ℂ) + I * b)).re * (a - 1/2) := by
    rcases lt_trichotomy a (1/2) with h | h | h
    · have hcont : ContinuousOn g (Icc a (1/2)) := fun v hv =>
        (hderiv v (by linarith [hv.1])).continuousAt.continuousWithinAt
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g
        (fun u => 2 * (Complex.digamma ((u : ℂ) + I * b)).re) h hcont
        (fun v hv => hderiv v (by linarith [hv.1]))
      refine ⟨c, by linarith [hc.1], by linarith [hc.2], ?_⟩
      have hne : (1/2 : ℝ) - a ≠ 0 := by linarith
      rw [hcd, div_mul_eq_mul_div, eq_div_iff hne]; ring
    · subst h; exact ⟨1/2, by norm_num, by norm_num, by ring⟩
    · have hcont : ContinuousOn g (Icc (1/2) a) := fun v hv =>
        (hderiv v (by linarith [hv.1])).continuousAt.continuousWithinAt
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g
        (fun u => 2 * (Complex.digamma ((u : ℂ) + I * b)).re) h hcont
        (fun v hv => hderiv v (by linarith [hv.1]))
      refine ⟨c, by linarith [hc.1], by linarith [hc.2], ?_⟩
      have hne : a - 1/2 ≠ 0 := by linarith
      rw [hcd, div_mul_eq_mul_div, eq_div_iff hne]
  obtain ⟨c, hc0, hc1, hcd⟩ := key
  have hdn := digamma_near_log c b hc0 hc1 hb
  set A := ‖Complex.Gamma ((a : ℂ) + I * b)‖
  set B := ‖Complex.Gamma (((1/2 : ℝ) : ℂ) + I * b)‖
  have hA : 0 < A := norm_pos_iff.mpr (gamma_line_ne b a ha0)
  have hB : 0 < B := norm_pos_iff.mpr (gamma_line_ne b (1/2) (by norm_num))
  have e1 : g a = 2 * Real.log A := by
    change Real.log (A^2) = _; rw [Real.log_pow]; norm_num
  have e2 : g (1/2) = 2 * Real.log B := by
    change Real.log (B^2) = _; rw [Real.log_pow]; norm_num
  have hbpos : 0 < |b| := by linarith
  have key2 : Real.log A ≤ Real.log B + (a - 1/2) * Real.log |b| + 5/2 := by
    rw [e1, e2] at hcd
    set r := (Complex.digamma ((c : ℂ) + I * b)).re
    have h1 : (a - 1/2) * (r - Real.log |b|) ≤ 5/2 := by
      have : |(a - 1/2) * (r - Real.log |b|)| ≤ 5/2 := by
        rw [abs_mul]
        have : |a - 1/2| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
        nlinarith [abs_nonneg (a - 1/2), abs_nonneg (r - Real.log |b|)]
      exact (abs_le.mp this).2
    nlinarith
  have : A ≤ B * Real.exp ((a - 1/2) * Real.log |b| + 5/2) := by
    rw [← Real.log_le_log_iff hA (by positivity), Real.log_mul hB.ne' (by positivity),
      Real.log_exp]
    linarith
  calc A ≤ B * Real.exp ((a - 1/2) * Real.log |b| + 5/2) := this
    _ = Real.exp (5/2) * |b| ^ (a - 1/2) * B := by
      rw [Real.rpow_def_of_pos hbpos, Real.exp_add]; ring_nf

lemma gamma_half (b : ℝ) :
    ‖Complex.Gamma (((1/2 : ℝ) : ℂ) + I * b)‖ ≤ Real.sqrt (2 * π) * Real.exp (-(π * |b|) / 2) := by
  set z : ℂ := ((1/2 : ℝ) : ℂ) + I * b with hz
  have h := Complex.Gamma_mul_Gamma_one_sub z
  have hconj : 1 - z = (starRingEnd ℂ) z := by
    apply Complex.ext <;> simp [hz] <;> norm_num
  rw [hconj, Complex.Gamma_conj, Complex.mul_conj] at h
  have hsin : Complex.sin (π * z) = ((Real.cosh (π * b) : ℝ) : ℂ) := by
    have : (π:ℂ) * z = ((π * b : ℝ) : ℂ) * I + π / 2 := by
      rw [hz]; push_cast; ring
    rw [this, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hsin] at h
  have hcosh : 0 < Real.cosh (π * b) := Real.cosh_pos _
  have hn : Complex.normSq (Complex.Gamma z) = π / Real.cosh (π * b) := by
    exact_mod_cast h
  rw [Complex.normSq_eq_norm_sq] at hn
  have hch : Real.exp (π * |b|) / 2 ≤ Real.cosh (π * b) := by
    rw [Real.cosh_eq]
    rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg hb]; have := Real.exp_pos (-(π * b)); linarith
    · rw [abs_of_nonpos hb]
      have := Real.exp_pos (π * b)
      have e : Real.exp (π * -b) = Real.exp (-(π * b)) := by ring_nf
      linarith
  have hsq : ‖Complex.Gamma z‖ ^ 2 ≤ (Real.sqrt (2 * π) * Real.exp (-(π * |b|) / 2)) ^ 2 := by
    rw [hn, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    have : ((2:ℕ):ℝ) * (-(π * |b|) / 2) = -(π * |b|) := by push_cast; ring
    rw [this, Real.exp_neg, div_le_iff₀ hcosh]
    have hep := Real.exp_pos (π * |b|)
    have : 2 * π * (Real.exp (π * |b|))⁻¹ * Real.cosh (π * b) ≥
        2 * π * (Real.exp (π * |b|))⁻¹ * (Real.exp (π * |b|) / 2) := by
      apply mul_le_mul_of_nonneg_left hch (by positivity)
    have h2 : 2 * π * (Real.exp (π * |b|))⁻¹ * (Real.exp (π * |b|) / 2) = π := by
      field_simp
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq

lemma gamma_bound (a b : ℝ) (ha0 : 1/2 ≤ a) (ha1 : a ≤ 3/2) (hb : 1 ≤ |b|) :
    ‖Complex.Gamma ((a : ℂ) + I * b)‖ ≤
      2 * Real.exp (5/2) * Real.sqrt (2 * π) * |b| ^ (a - 1/2) * Real.exp (-(π * |b|) / 2) := by
  have hbpos : 0 < |b| := by linarith
  rcases le_or_gt a 1 with h | h
  · have h1 := gamma_ratio a b (by linarith) h hb
    have h2 := gamma_half b
    calc ‖Complex.Gamma ((a : ℂ) + I * b)‖ ≤ Real.exp (5/2) * |b| ^ (a - 1/2) *
          (Real.sqrt (2 * π) * Real.exp (-(π * |b|) / 2)) := by
          refine h1.trans ?_
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := by
          have : 0 ≤ Real.exp (5/2) * |b| ^ (a - 1/2) * (Real.sqrt (2 * π) * Real.exp (-(π * |b|) / 2)) := by
            positivity
          nlinarith
  · have hs : ((a - 1 : ℝ) : ℂ) + I * b ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have heq : ((a : ℂ) + I * b) = (((a - 1 : ℝ) : ℂ) + I * b) + 1 := by push_cast; ring
    rw [heq, Complex.Gamma_add_one _ hs, norm_mul]
    have h1 := gamma_ratio (a - 1) b (by linarith) (by linarith) hb
    have h2 := gamma_half b
    have hn : ‖((a - 1 : ℝ) : ℂ) + I * b‖ ≤ 2 * |b| := by
      calc ‖((a - 1 : ℝ) : ℂ) + I * b‖ ≤ ‖((a - 1 : ℝ) : ℂ)‖ + ‖I * b‖ := norm_add_le _ _
        _ = |a - 1| + |b| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 2 * |b| := by rw [abs_of_pos (by linarith)]; linarith
    have hpow : |b| * |b| ^ (a - 1 - 1/2) = |b| ^ (a - 1/2) := by
      rw [← Real.rpow_one_add' hbpos.le (by linarith)]; ring_nf
    calc ‖((a - 1 : ℝ) : ℂ) + I * b‖ * ‖Complex.Gamma (((a - 1 : ℝ) : ℂ) + I * b)‖
        ≤ (2 * |b|) * (Real.exp (5/2) * |b| ^ (a - 1 - 1/2) *
            (Real.sqrt (2 * π) * Real.exp (-(π * |b|) / 2))) := by
          apply mul_le_mul hn (h1.trans ?_) (norm_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * Real.exp (5/2) * Real.sqrt (2 * π) * (|b| * |b| ^ (a - 1 - 1/2)) *
            Real.exp (-(π * |b|) / 2) := by ring
      _ = _ := by rw [hpow]

lemma norm_cos_le (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact neg_le_abs _
  have h2 : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact le_abs_self _
  rw [norm_div]
  have : ‖(2:ℂ)‖ = 2 := by simp
  rw [this]
  calc ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ / 2 ≤
      (‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ ≤ Real.exp |z.im| := by linarith

/-- the functional-equation bound -/
lemma zeta_fe_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, -1/2 ≤ w.re → w.re ≤ 1/2 → 1 ≤ |w.im| →
    ‖riemannZeta w‖ ≤ C * |w.im| ^ (1/2 - w.re) * ‖riemannZeta (1 - w)‖ := by
  set C0 := 2 * Real.exp (5/2) * Real.sqrt (2 * π)
  refine ⟨2 * C0, by positivity, fun w h1 h2 h3 => ?_⟩
  have hw0 : w ≠ 0 := by intro h; rw [h] at h3; simp at h3; linarith
  have hs : ∀ n : ℕ, (1 - w) ≠ -n := by
    intro n h; have := congrArg Complex.re h; simp at this
    have : (0:ℝ) ≤ n := n.cast_nonneg; linarith
  have hs1 : (1 - w) ≠ 1 := by intro h; apply hw0; linear_combination -h
  have hfe := riemannZeta_one_sub hs hs1
  rw [sub_sub_cancel] at hfe
  rw [hfe]
  have hpi : (2 * (π:ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have hcp : ‖(2 * (π:ℂ)) ^ (-(1 - w))‖ ≤ 1 := by
    rw [hpi, norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
    simp; linarith
  have hg : ‖Complex.Gamma (1 - w)‖ ≤ C0 * |w.im| ^ (1/2 - w.re) * Real.exp (-(π * |w.im|) / 2) := by
    have heq : 1 - w = (((1 - w.re : ℝ)) : ℂ) + I * (-w.im : ℝ) := by
      apply Complex.ext <;> simp
    rw [heq]
    have := gamma_bound (1 - w.re) (-w.im) (by linarith) (by linarith) (by rw [abs_neg]; exact h3)
    rw [abs_neg] at this
    convert this using 3; ring
  have hc : ‖Complex.cos (π * (1 - w) / 2)‖ ≤ Real.exp (π * |w.im| / 2) := by
    refine (norm_cos_le _).trans (le_of_eq ?_)
    congr 1
    have : (π * (1 - w) / 2).im = -(π * w.im / 2) := by simp; ring
    rw [this, abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos]; norm_num
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have h2n : ‖(2:ℂ)‖ = 2 := by simp
  rw [h2n]
  have hexp : Real.exp (-(π * |w.im|) / 2) * Real.exp (π * |w.im| / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hz := norm_nonneg (riemannZeta (1 - w))
  calc 2 * ‖(2 * (π:ℂ)) ^ (-(1 - w))‖ * ‖Complex.Gamma (1 - w)‖ *
        ‖Complex.cos (π * (1 - w) / 2)‖ * ‖riemannZeta (1 - w)‖
      ≤ 2 * 1 * (C0 * |w.im| ^ (1/2 - w.re) * Real.exp (-(π * |w.im|) / 2)) *
        Real.exp (π * |w.im| / 2) * ‖riemannZeta (1 - w)‖ := by gcongr
    _ = 2 * C0 * |w.im| ^ (1/2 - w.re) * ‖riemannZeta (1 - w)‖ *
        (Real.exp (-(π * |w.im|) / 2) * Real.exp (π * |w.im| / 2)) := by ring
    _ = _ := by rw [hexp, mul_one]

/-- absolutely convergent region -/
lemma zeta_le_const (s : ℂ) (hs : 5/4 ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / ((n:ℝ) + 1) ^ (5/4 : ℝ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith)]
  have hsum : Summable (fun n : ℕ => 1 / ((n:ℝ) + 1) ^ (5/4 : ℝ)) := by
    have := (Real.summable_one_div_nat_rpow (p := 5/4)).mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr this |>.congr (fun n => by push_cast; ring_nf)
  have hle : ∀ n : ℕ, ‖1 / ((n:ℂ) + 1) ^ s‖ ≤ 1 / ((n:ℝ) + 1) ^ (5/4 : ℝ) := by
    intro n
    have : ((n:ℂ) + 1) = (((n:ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_div, norm_one, norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]) hs
  calc ‖∑' n : ℕ, 1 / ((n:ℂ) + 1) ^ s‖ ≤ ∑' n : ℕ, ‖1 / ((n:ℂ) + 1) ^ s‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum)
    _ ≤ _ := Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum) hsum

/-- the left line -/
lemma zeta_left (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1/4) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ,
    w.re = -1/2 + η → 1 ≤ |w.im| → ‖riemannZeta w‖ ≤ C * |w.im| ^ (1 - η) := by
  obtain ⟨C, hC0, hC⟩ := zeta_fe_bound
  set Z := ∑' n : ℕ, 1 / ((n:ℝ) + 1) ^ (5/4 : ℝ)
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => by positivity)
  refine ⟨C * Z, by positivity, fun w hw h3 => ?_⟩
  have h := hC w (by linarith) (by linarith) h3
  have hz := zeta_le_const (1 - w) (by simp; linarith)
  rw [hw] at h
  have he : (1/2 : ℝ) - (-1/2 + η) = 1 - η := by ring
  rw [he] at h
  calc ‖riemannZeta w‖ ≤ C * |w.im| ^ (1 - η) * ‖riemannZeta (1 - w)‖ := h
    _ ≤ C * |w.im| ^ (1 - η) * Z := by gcongr
    _ = C * Z * |w.im| ^ (1 - η) := by ring

/-- crude growth on `-1/2+η ≤ re ≤ 2` -/
lemma zeta_crude (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1/4) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ,
    -1/2 + η ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| → ‖riemannZeta w‖ ≤ C * (1 + |w.im|) ^ (2 - η) := by
  obtain ⟨C, hC0, hC⟩ := zeta_fe_bound
  refine ⟨6 * C + 6, by positivity, fun w h1 h2 h3 => ?_⟩
  have ht : 1 ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
  have hw1 : w ≠ 1 := by intro h; rw [h] at h3; simp at h3; linarith
  have hnorm : ‖w‖ ≤ 2 + |w.im| := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 2 + |w.im| := by gcongr; rw [abs_le]; constructor <;> linarith
  have hgen : ∀ u : ℂ, 1/2 ≤ u.re → u.re ≤ 2 → 1 ≤ |u.im| → ‖riemannZeta u‖ ≤ 6 * (1 + |u.im|) := by
    intro u hu1 hu2 hu3
    have hu1' : u ≠ 1 := by intro h; rw [h] at hu3; simp at hu3; linarith
    have hb := Zeta23.RvM.norm_riemannZeta_le_of_re_pos (s := u) (by linarith) hu1'
    have h1u : 1 ≤ ‖1 - u‖ := by
      have := Complex.abs_im_le_norm (1 - u); simp at this; linarith
    have hun : ‖u‖ ≤ 2 + |u.im| := by
      calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
        _ ≤ 2 + |u.im| := by gcongr; rw [abs_le]; constructor <;> linarith
    have : 1 / ‖1 - u‖ ≤ 1 := by rw [div_le_one (by linarith)]; exact h1u
    have : ‖u‖ / u.re ≤ 2 * ‖u‖ := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg u]
    linarith [abs_nonneg u.im]
  rcases le_or_gt (1/2) w.re with hr | hr
  · have := hgen w hr h2 h3
    calc ‖riemannZeta w‖ ≤ 6 * (1 + |w.im|) := this
      _ ≤ 6 * (1 + |w.im|) ^ (2 - η) := by
          gcongr
          calc (1 + |w.im|) = (1 + |w.im|) ^ (1:ℝ) := (Real.rpow_one _).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ht (by linarith)
      _ ≤ _ := by gcongr; linarith
  · have h := hC w (by linarith) hr.le h3
    have hz := hgen (1 - w) (by simp; linarith) (by simp; linarith) (by simpa using h3)
    simp only [sub_im, one_im, zero_sub, abs_neg] at hz
    have hp : |w.im| ^ (1/2 - w.re) ≤ (1 + |w.im|) ^ (1 - η) := by
      calc |w.im| ^ (1/2 - w.re) ≤ (1 + |w.im|) ^ (1/2 - w.re) := by
            apply Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by linarith)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ht (by linarith)
    have hsplit : (1 + |w.im|) ^ (2 - η) = (1 + |w.im|) ^ (1 - η) * (1 + |w.im|) := by
      rw [show (2 - η) = (1 - η) + 1 by ring, Real.rpow_add (by linarith), Real.rpow_one]
    calc ‖riemannZeta w‖ ≤ C * |w.im| ^ (1/2 - w.re) * ‖riemannZeta (1 - w)‖ := h
      _ ≤ C * (1 + |w.im|) ^ (1 - η) * (6 * (1 + |w.im|)) := by gcongr
      _ = 6 * C * (1 + |w.im|) ^ (2 - η) := by rw [hsplit]; ring
      _ ≤ _ := by gcongr; linarith

/-- `1/ζ` is bounded on `re ≥ 2` -/
lemma inv_zeta_le_three (s : ℂ) (hs : 2 ≤ s.re) : ‖(riemannZeta s)⁻¹‖ ≤ 3 := by
  have h := Zeta23.RvM.norm_riemannZeta_sub_one_le hs
  have hpi : π ^ 2 / 6 - 1 ≤ 2/3 := by
    have h1 := Real.pi_lt_d2
    have h2 := Real.pi_pos
    nlinarith
  have : 1/3 ≤ ‖riemannZeta s‖ := by
    have e : (1:ℂ) - (1 - riemannZeta s) = riemannZeta s := by ring
    have h3 := norm_sub_norm_le (1:ℂ) (1 - riemannZeta s)
    rw [e, norm_one] at h3
    rw [norm_sub_rev] at h
    linarith
  rw [norm_inv]
  calc ‖riemannZeta s‖⁻¹ ≤ (1/3)⁻¹ := inv_anti₀ (by norm_num) this
    _ = 3 := by norm_num

end VerjZeta
end V2

section V3

open Complex Filter Topology Set MeasureTheory

namespace VerjShift

lemma rect_mem (a b p T : ℝ) (hap : a < p) (hpb : p < b) (hT : 0 < T) :
    Rectangle ((a : ℂ) - T * I) (b + T * I) ∈ 𝓝 (p : ℂ) := by
  have hsub : (Ioo a b ×ℂ Ioo (-T) T) ⊆ Rectangle ((a : ℂ) - T * I) (b + T * I) := by
    intro z hz
    have e1 : ((a:ℂ) - T*I).re = a := by simp
    have e2 : ((a:ℂ) - T*I).im = -T := by simp
    have e3 : ((b:ℂ) + T*I).re = b := by simp
    have e4 : ((b:ℂ) + T*I).im = T := by simp
    simp only [Rectangle, mem_reProdIm, e1, e2, e3, e4] at hz ⊢
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩
  apply Filter.mem_of_superset _ hsub
  apply (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds
  simp only [mem_reProdIm, ofReal_re, ofReal_im, mem_Ioo]
  exact ⟨⟨hap, hpb⟩, ⟨by linarith, hT⟩⟩

theorem shift (h : ℂ → ℂ) (a b p : ℝ) (A : ℂ) (hap : a < p) (hpb : p < b)
    (hol : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s ≠ p → DifferentiableAt ℂ h s)
    (near : (h - fun s => A / (s - p)) =O[𝓝[≠] (p:ℂ)] (1 : ℂ → ℂ))
    (intL : Integrable (fun t : ℝ => h (a + t * I)))
    (intR : Integrable (fun t : ℝ => h (b + t * I)))
    (top : Tendsto (fun T : ℝ => ∫ x in a..b, h (x + T * I)) atTop (𝓝 0))
    (bot : Tendsto (fun T : ℝ => ∫ x in a..b, h (x + (-T) * I)) atTop (𝓝 0)) :
    (∫ t : ℝ, h (b + t * I)) - ∫ t : ℝ, h (a + t * I) = 2 * Real.pi * A := by
  have key : ∀ T : ℝ, 0 < T →
      (∫ x in a..b, h (x + (-T) * I)) - (∫ x in a..b, h (x + T * I)) +
        I * (∫ y in (-T)..T, h (b + y * I)) - I * (∫ y in (-T)..T, h (a + y * I)) =
        2 * Real.pi * I * A := by
    intro T hT
    have hres := ResidueTheoremOnRectangleWithSimplePole_prime (f := h) (p := (p:ℂ)) (A := A)
      (z := (a : ℂ) - T * I) (w := b + T * I) (by simp; linarith) (by simp; linarith)
      (rect_mem a b p T hap hpb hT) ?_ near
    · simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul] at hres
      have e1 : ((a:ℂ) - T*I).re = a := by simp
      have e2 : ((a:ℂ) - T*I).im = -T := by simp
      have e3 : ((b:ℂ) + T*I).re = b := by simp
      have e4 : ((b:ℂ) + T*I).im = T := by simp
      rw [e1, e2, e3, e4] at hres
      have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      rw [one_div, inv_mul_eq_iff_eq_mul₀ h2] at hres
      push_cast at hres
      linear_combination hres
    · intro z hz
      have hz1 := hz.1
      simp only [Rectangle, mem_reProdIm] at hz1
      have h1 := hz1.1
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, add_re] at h1
      norm_num at h1
      rw [Set.uIcc_of_le (by linarith)] at h1
      exact (hol z h1.1 h1.2 hz.2).differentiableWithinAt
  have tR := intervalIntegral_tendsto_integral intR tendsto_neg_atTop_atBot tendsto_id
  have tL := intervalIntegral_tendsto_integral intL tendsto_neg_atTop_atBot tendsto_id
  have lim := ((bot.sub top).add (tR.const_mul I)).sub (tL.const_mul I)
  have lim2 : Tendsto (fun T : ℝ =>
      (∫ x in a..b, h (x + (-T) * I)) - (∫ x in a..b, h (x + T * I)) +
        I * (∫ y in (-T)..T, h (b + y * I)) - I * (∫ y in (-T)..T, h (a + y * I)))
      atTop (𝓝 (2 * Real.pi * I * A)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact (key T hT).symm
  have := tendsto_nhds_unique lim lim2
  have hI : I ≠ 0 := I_ne_zero
  apply mul_left_cancel₀ hI
  linear_combination this

end VerjShift
end V3

section V4

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace VerjDir

open ArithmeticFunction in
open scoped ArithmeticFunction.zeta in
lemma totient_LSeries (s : ℂ) (hs : 2 < s.re) :
    ∑' k : ℕ, (((k+1 : ℕ).totient : ℕ) : ℂ) * (((k+1 : ℕ) : ℂ) ^ (-s)) =
      riemannZeta (s - 1) / riemannZeta s := by
  let Φ : ArithmeticFunction ℂ := ⟨fun n => ((n.totient : ℕ) : ℂ), by simp⟩
  have hΦ : ∀ n, Φ n = ((n.totient : ℕ) : ℂ) := fun n => rfl
  have hmul : (fun n => (Φ * (ζ : ArithmeticFunction ℂ)) n) = fun n : ℕ => (n : ℂ) := by
    funext n
    rw [coe_mul_zeta_apply]
    simp only [hΦ]
    exact_mod_cast Nat.sum_totient n
  have hsΦ : LSeriesSummable (fun n => Φ n) s := by
    apply LSeriesSummable_of_le_const_mul_rpow (x := 2) hs
    refine ⟨1, fun n hn => ?_⟩
    rw [hΦ, Complex.norm_natCast, one_mul]
    norm_num
    exact_mod_cast Nat.totient_le n
  have hsζ : LSeriesSummable (fun n => (ζ : ArithmeticFunction ℂ) n) s :=
    LSeriesSummable_zeta_iff.mpr (by linarith)
  have hL := LSeries_mul' hsΦ hsζ
  simp only [ArithmeticFunction.natCoe_apply] at hL
  rw [hmul, LSeries_zeta_eq_riemannZeta (by linarith)] at hL
  have hid : LSeries (fun n : ℕ => (n : ℂ)) s = riemannZeta (s - 1) := by
    rw [← LSeries_one_eq_riemannZeta (by simp; linarith)]
    unfold LSeries
    congr 1; funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [cpow_sub _ _ hn0, cpow_one]
    simp only [Pi.one_apply]
    field_simp
  rw [hid] at hL
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hLΦ : LSeries (fun n => Φ n) s = riemannZeta (s - 1) / riemannZeta s := by
    rw [hL]; field_simp
  rw [← hLΦ]
  unfold LSeries
  rw [hsΦ.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add]
  congr 1; funext k
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), hΦ, cpow_neg, div_eq_mul_inv]

end VerjDir

namespace VerjMellin.Good
variable {f : ℝ → ℝ} {α β : ℝ} (G : Good f α β)
include G

/-- the discrete sum as a vertical integral on `Re s = 3` -/
lemma sum_eq_integral (δ : ℝ) (hδ : 0 < δ) :
    ((∑' k : ℕ, ((k+1 : ℕ).totient : ℝ) * f (δ * (k+1 : ℕ)) : ℝ) : ℂ) =
      (1 / (2 * π)) * ∫ t : ℝ, (δ : ℂ) ^ (-((3:ℂ) + t * I)) *
        mellin (fun x => (f x : ℂ)) ((3:ℂ) + t * I) *
        (riemannZeta ((3:ℂ) + t * I - 1) / riemannZeta ((3:ℂ) + t * I)) := by
  set F := mellin (fun x => (f x : ℂ))
  have hVI := G.verticalIntegrable 3 (by norm_num) le_rfl
  unfold VerticalIntegrable at hVI
  -- term functions
  set T : ℕ → ℝ → ℂ := fun k t => (((k+1 : ℕ).totient : ℕ) : ℂ) *
    (((δ * (k+1 : ℕ) : ℝ) : ℂ) ^ (-((3:ℂ) + t * I)) * F ((3:ℂ) + t * I)) with hT
  have hnorm : ∀ k t, ‖T k t‖ = ((k+1 : ℕ).totient : ℝ) * (δ * (k+1 : ℕ)) ^ (-(3:ℝ)) *
      ‖F ((3:ℂ) + t * I)‖ := by
    intro k t
    simp only [hT, norm_mul, Complex.norm_natCast]
    rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp; ring
  have hint : ∀ k, Integrable (T k) := by
    intro k
    refine (hVI.norm.const_mul (((k+1 : ℕ).totient : ℝ) * (δ * (k+1 : ℕ)) ^ (-(3:ℝ)))).mono' ?_ ?_
    · simp only [hT]
      refine AEStronglyMeasurable.const_mul ?_ _
      refine Continuous.aestronglyMeasurable ?_
      refine Continuous.mul ?_ (G.differentiable.continuous.comp (by fun_prop))
      refine Continuous.const_cpow (by fun_prop) (Or.inl (by
        have : (0:ℝ) < δ * (k+1 : ℕ) := by positivity
        exact_mod_cast this.ne'))
    · filter_upwards with t
      rw [hnorm]; push_cast; exact le_refl _
  have hsum : Summable fun k => ∫ t, ‖T k t‖ := by
    simp only [hnorm]
    simp only [integral_const_mul]
    apply Summable.mul_right
    have hs : Summable (fun k : ℕ => δ ^ (-(3:ℝ)) * (((k+1 : ℕ) : ℝ) ^ (-(2:ℝ)))) := by
      apply Summable.mul_left
      have := (Real.summable_nat_rpow (p := -(2:ℝ))).mpr (by norm_num)
      exact (summable_nat_add_iff 1).mpr this |>.congr (fun n => by push_cast; ring_nf)
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
    have hk : (0:ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
    rw [Real.mul_rpow hδ.le hk.le]
    have h3 : ((k+1 : ℕ) : ℝ) ^ (-(3:ℝ)) = ((k+1 : ℕ) : ℝ) ^ (-(2:ℝ)) / ((k+1 : ℕ) : ℝ) := by
      rw [show (-(3:ℝ)) = -(2:ℝ) - 1 by norm_num, Real.rpow_sub hk, Real.rpow_one]
    rw [h3]
    have htot : ((k+1 : ℕ).totient : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le _
    have hd : 0 ≤ δ ^ (-(3:ℝ)) := by positivity
    have h2 : 0 ≤ ((k+1 : ℕ) : ℝ) ^ (-(2:ℝ)) := by positivity
    calc ((k+1 : ℕ).totient : ℝ) * (δ ^ (-(3:ℝ)) * (((k+1 : ℕ) : ℝ) ^ (-(2:ℝ)) / ((k+1 : ℕ) : ℝ)))
        ≤ ((k+1 : ℕ) : ℝ) * (δ ^ (-(3:ℝ)) * (((k+1 : ℕ) : ℝ) ^ (-(2:ℝ)) / ((k+1 : ℕ) : ℝ))) := by
          gcongr
      _ = _ := by field_simp
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  -- each term
  have hterm : ∀ k : ℕ, ((((k+1 : ℕ).totient : ℝ) * f (δ * (k+1 : ℕ)) : ℝ) : ℂ) =
      (1 / (2 * π)) * ∫ t, T k t := by
    intro k
    have hx : (0:ℝ) < δ * (k+1 : ℕ) := by positivity
    have hinv := G.inversion _ hx
    unfold mellinInv at hinv
    rw [Complex.ofReal_mul, ← hinv]
    simp only [hT, Complex.real_smul, smul_eq_mul, integral_const_mul]
    push_cast
    ring
  rw [Complex.ofReal_tsum]
  simp only [hterm]
  rw [tsum_mul_left, hswap]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [hT]
  have hre : (2:ℝ) < ((3:ℂ) + t * I).re := by simp; norm_num
  rw [← VerjDir.totient_LSeries _ hre, ← tsum_mul_left]
  congr 1; funext k
  have hk : (0:ℝ) ≤ ((k+1 : ℕ) : ℝ) := by positivity
  rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg hδ.le hk]
  push_cast
  ring

end VerjMellin.Good
end V4

section V5a

open Complex Filter Topology Set MeasureTheory

namespace VerjZi

/-- `1/ζ` with the removable value `0` at `s = 1`. -/
noncomputable def Zi (s : ℂ) : ℂ := if s = 1 then 0 else (riemannZeta s)⁻¹

lemma zeta_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1/2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro h
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 h
  have := hRH s h (by
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith) hs1
  linarith

lemma Zi_eq_of_ne {s : ℂ} (hs : s ≠ 1) : Zi s = (riemannZeta s)⁻¹ := by
  simp [Zi, hs]

lemma Zi_continuousAt_one : ContinuousAt Zi 1 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  have h0 : Zi 1 = 0 := by simp [Zi]
  rw [h0]
  have hO := inv_riemannZeta_isBigO
  have ht : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1:ℂ)) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - 1) (𝓝 (1:ℂ)) (𝓝 (1 - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 := hO.trans_tendsto ht
  apply h1.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (Zi_eq_of_ne hs).symm

lemma Zi_differentiableAt (hRH : RiemannHypothesis) {s : ℂ} (hs : 1/2 < s.re) :
    DifferentiableAt ℂ Zi s := by
  have hne : ∀ z : ℂ, 1/2 < z.re → z ≠ 1 → DifferentiableAt ℂ Zi z := by
    intro z hz hz1
    have hd : DifferentiableAt ℂ (fun w => (riemannZeta w)⁻¹) z :=
      (differentiableAt_riemannZeta hz1).inv (zeta_ne_zero_of_RH hRH hz hz1)
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
    exact Zi_eq_of_ne hw
  by_cases hs1 : s = 1
  · subst hs1
    have hball : Metric.ball (1:ℂ) (1/2) ∈ 𝓝 (1:ℂ) := Metric.ball_mem_nhds _ (by norm_num)
    have hdiff : DifferentiableOn ℂ Zi (Metric.ball (1:ℂ) (1/2) \ {1}) := by
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      apply hne z _ hz.2
      have := hz.1
      rw [Metric.mem_ball, dist_eq_norm] at this
      have h2 := Complex.abs_re_le_norm (z - 1)
      rw [Complex.sub_re, Complex.one_re] at h2
      have := abs_lt.mp (lt_of_le_of_lt h2 this)
      linarith [this.1]
    have := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hball).mp
      ⟨hdiff, Zi_continuousAt_one⟩
    exact this.differentiableAt hball
  · exact hne s hs hs1

lemma Zi_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = Zi s := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  rw [Zi_eq_of_ne hs1]
  have h := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h
  have hz : riemannZeta s ≠ 0 := by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  field_simp
  rw [mul_comm]; exact h

/-- Growth of `Zi` in a strip to the right of the critical line, under RH. -/
lemma Zi_growth (hRH : RiemannHypothesis) (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1/2 + δ ≤ s.re → s.re ≤ 2 → ‖Zi s‖ ≤ B * (1 + |s.im|) ^ ε := by
  obtain ⟨C, hC⟩ := Titchmarsh.inv_riemannZeta_le_rpow_of_riemannHypothesis hRH δ hδ ε hε
  have hK : IsCompact (Icc (1/2 + δ) 2 ×ℂ Icc (-1:ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn Zi (Icc (1/2 + δ) 2 ×ℂ Icc (-1:ℝ) 1) := by
    intro z hz
    have : 1/2 < z.re := by have := hz.1.1; linarith
    exact (Zi_differentiableAt hRH this).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max |C| |M|, by positivity, ?_⟩
  intro s hs1 hs2
  have hp : 1 ≤ (1 + |s.im|) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hε.le
  by_cases him : 1 ≤ |s.im|
  · have hs1' : s ≠ 1 := by rintro rfl; simp at him; norm_num at him
    rw [Zi_eq_of_ne hs1']
    calc ‖(riemannZeta s)⁻¹‖ ≤ C * |s.im| ^ ε := hC s hs1 hs2 him
      _ ≤ |C| * (1 + |s.im|) ^ ε := by
          apply mul_le_mul (le_abs_self C) _ (by positivity) (abs_nonneg C)
          exact Real.rpow_le_rpow (abs_nonneg _) (by linarith) hε.le
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · push Not at him
    have hmem : s ∈ Icc (1/2 + δ) 2 ×ℂ Icc (-1:ℝ) 1 := by
      refine ⟨⟨hs1, hs2⟩, ?_, ?_⟩ <;> linarith [abs_lt.mp him]
    calc ‖Zi s‖ ≤ M := hM s hmem
      _ ≤ |M| := le_abs_self M
      _ ≤ max |C| |M| * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ _ := by gcongr


lemma integrable_of_bound (u : ℝ → ℂ) (hu : Continuous u) (r : ℝ) (hr : 1 < r) (M : ℝ)
    (h : ∀ t : ℝ, 1 ≤ |t| → ‖u t‖ ≤ M * (1 + |t|) ^ (-r)) : Integrable u := by
  have hg : Integrable (fun t : ℝ => M * (1 + |t|) ^ (-r)) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
    exact (this.const_mul M).congr (by filter_upwards with t; simp [Real.norm_eq_abs])
  have h1 : IntegrableOn u (Icc (-1) 1) := hu.integrableOn_Icc
  have h2 : IntegrableOn u (Icc (-1:ℝ) 1)ᶜ := by
    refine Integrable.mono' hg.integrableOn hu.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc.compl (fun t ht => h t ?_)
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have := h1.union h2
  rwa [union_compl_self, integrableOn_univ] at this

lemma rpow_combine (u a b : ℝ) (hu : 0 < u) :
    u ^ a * u ^ b / u ^ (2:ℕ) = u ^ (a + b - 2) := by
  rw [Real.rpow_sub hu, Real.rpow_add hu]; norm_cast

/-- `F(s) ζ(s-1) / ζ(s)` -/
noncomputable def kf (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  mellin (fun x => (f x : ℂ)) s * riemannZeta (s - 1) * Zi s

end VerjZi

namespace VerjMellin.Good
open VerjZi
variable {f : ℝ → ℝ} {α β : ℝ} (G : Good f α β)
include G

lemma kf_differentiableAt (hRH : RiemannHypothesis) (s : ℂ) (hs : 1/2 < s.re) (hs2 : s ≠ 2) :
    DifferentiableAt ℂ (kf f) s := by
  have h1 : s - 1 ≠ 1 := by intro h; apply hs2; linear_combination h
  have hz : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (s - 1)) s :=
    (differentiableAt_riemannZeta h1).comp s (differentiableAt_id.sub_const 1)
  exact ((G.differentiable s).mul hz).mul (Zi_differentiableAt hRH hs)

lemma kf_continuous_line (hRH : RiemannHypothesis) (c : ℝ) (hc : 1/2 < c) (hc2 : c ≠ 2) :
    Continuous (fun t : ℝ => kf f ((c : ℂ) + t * I)) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hd := G.kf_differentiableAt hRH ((c : ℂ) + t * I) (by simpa using hc) (by
    intro h; apply hc2; have := congrArg Complex.re h; simpa using this)
  exact hd.continuousAt.comp (f := fun t : ℝ => (c : ℂ) + t * I) (x := t)
    (Continuous.continuousAt (by fun_prop))

lemma kf_bound_strip (hRH : RiemannHypothesis) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1/4) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 1/2 + η ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
      ‖kf f s‖ ≤ M * (1 + |s.im|) ^ (-(η/2)) := by
  obtain ⟨K, hK0, hK⟩ := G.decay
  obtain ⟨C, hC0, hC⟩ := VerjZeta.zeta_crude η hη0 hη1
  obtain ⟨B, hB0, hB⟩ := Zi_growth hRH η hη0 (η/2) (by linarith)
  refine ⟨K * C * (B + 3), by positivity, fun s h1 h3 him => ?_⟩
  set u := 1 + |s.im| with hu
  have hu1 : 1 ≤ u := by linarith [abs_nonneg s.im]
  have hu0 : 0 < u := by linarith
  have hF := hK s (by linarith) h3
  have hz := hC (s - 1) (by simp; linarith) (by simp; linarith) (by simpa using him)
  simp only [sub_im, one_im, sub_zero] at hz
  have hZ : ‖Zi s‖ ≤ (B + 3) * u ^ (η/2) := by
    have hp : 1 ≤ u ^ (η/2) := Real.one_le_rpow hu1 (by linarith)
    rcases le_total s.re 2 with h2 | h2
    · calc ‖Zi s‖ ≤ B * u ^ (η/2) := hB s h1 h2
        _ ≤ _ := by gcongr; linarith
    · have hs1 : s ≠ 1 := by intro h; rw [h] at h2; norm_num at h2
      rw [Zi_eq_of_ne hs1]
      calc ‖(riemannZeta s)⁻¹‖ ≤ 3 := VerjZeta.inv_zeta_le_three s h2
        _ ≤ 3 * u ^ (η/2) := by linarith
        _ ≤ _ := by gcongr; linarith
  unfold kf
  rw [norm_mul, norm_mul]
  calc ‖mellin (fun x => (f x : ℂ)) s‖ * ‖riemannZeta (s - 1)‖ * ‖Zi s‖
      ≤ (K / u ^ 2) * (C * u ^ (2 - η)) * ((B + 3) * u ^ (η/2)) := by
        gcongr
    _ = K * C * (B + 3) * (u ^ (2 - η) * u ^ (η/2) / u ^ (2:ℕ)) := by ring
    _ = _ := by rw [rpow_combine _ _ _ hu0]; congr 2; ring

lemma kf_bound_left (hRH : RiemannHypothesis) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1/4) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖kf f (((1/2 + η : ℝ) : ℂ) + t * I)‖ ≤ M * (1 + |t|) ^ (-(1 + η/2)) := by
  obtain ⟨K, hK0, hK⟩ := G.decay
  obtain ⟨C, hC0, hC⟩ := VerjZeta.zeta_left η hη0 hη1
  obtain ⟨B, hB0, hB⟩ := Zi_growth hRH η hη0 (η/2) (by linarith)
  refine ⟨K * C * B, by positivity, fun t him => ?_⟩
  set s : ℂ := ((1/2 + η : ℝ) : ℂ) + t * I with hs
  have hre : s.re = 1/2 + η := by simp [hs]
  have him' : s.im = t := by simp [hs]
  set u := 1 + |t| with hu
  have hu1 : 1 ≤ u := by linarith [abs_nonneg t]
  have hu0 : 0 < u := by linarith
  have hF := hK s (by linarith) (by linarith)
  rw [him'] at hF
  have hz := hC (s - 1) (by simp [hre]; ring) (by simpa [him'] using him)
  simp only [sub_im, one_im, sub_zero, him'] at hz
  have hz' : ‖riemannZeta (s - 1)‖ ≤ C * u ^ (1 - η) := by
    calc _ ≤ C * |t| ^ (1 - η) := hz
      _ ≤ _ := by gcongr <;> linarith
  have hZ := hB s (by linarith) (by linarith)
  rw [him'] at hZ
  unfold kf
  rw [norm_mul, norm_mul]
  calc ‖mellin (fun x => (f x : ℂ)) s‖ * ‖riemannZeta (s - 1)‖ * ‖Zi s‖
      ≤ (K / u ^ 2) * (C * u ^ (1 - η)) * (B * u ^ (η/2)) := by
        gcongr
    _ = K * C * B * (u ^ (1 - η) * u ^ (η/2) / u ^ (2:ℕ)) := by ring
    _ = _ := by rw [rpow_combine _ _ _ hu0]; congr 2; ring

lemma kf_bound_right :
    ∃ M : ℝ, ∀ t : ℝ, ‖kf f ((3 : ℂ) + t * I)‖ ≤ M * (1 + |t|) ^ (-(2:ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := G.decay
  set Z := ∑' n : ℕ, 1 / ((n:ℝ) + 1) ^ (5/4 : ℝ)
  refine ⟨K * Z * 3, fun t => ?_⟩
  set s : ℂ := (3 : ℂ) + t * I with hs
  have hre : s.re = 3 := by simp [hs]
  have him' : s.im = t := by simp [hs]
  have hF := hK s (by linarith) (by linarith)
  rw [him'] at hF
  have hz := VerjZeta.zeta_le_const (s - 1) (by simp [hre]; norm_num)
  have hs1 : s ≠ 1 := by intro h; rw [h] at hre; norm_num at hre
  have hZ : ‖Zi s‖ ≤ 3 := by rw [Zi_eq_of_ne hs1]; exact VerjZeta.inv_zeta_le_three s (by linarith)
  set u := 1 + |t| with hu
  have hu0 : 0 < u := by linarith [abs_nonneg t]
  unfold kf
  rw [norm_mul, norm_mul]
  calc ‖mellin (fun x => (f x : ℂ)) s‖ * ‖riemannZeta (s - 1)‖ * ‖Zi s‖
      ≤ (K / u ^ 2) * Z * 3 := by gcongr
    _ = _ := by rw [Real.rpow_neg hu0.le, Real.rpow_two]; ring

end VerjMellin.Good
end V5a

section V5b

open Complex Filter Topology Set MeasureTheory

namespace VerjZi

lemma norm_dpow (δ : ℝ) (hδ : 0 < δ) (s : ℂ) : ‖(δ : ℂ) ^ (-s)‖ = δ ^ (-s.re) := by
  rw [norm_cpow_eq_rpow_re_of_pos hδ]; simp

lemma dpow_le (δ : ℝ) (hδ : 0 < δ) (a b x : ℝ) (hax : a ≤ x) (hxb : x ≤ b) :
    δ ^ (-x) ≤ δ ^ (-a) + δ ^ (-b) := by
  rcases le_total δ 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hδ h (show -b ≤ -x by linarith)
    linarith [Real.rpow_nonneg hδ.le (-a)]
  · have := Real.rpow_le_rpow_of_exponent_le h (show -x ≤ -a by linarith)
    linarith [Real.rpow_nonneg hδ.le (-b)]

end VerjZi

namespace VerjMellin.Good
open VerjZi
variable {f : ℝ → ℝ} {α β : ℝ} (G : Good f α β)
include G

lemma kf_int_left (hRH : RiemannHypothesis) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1/4) :
    Integrable (fun t : ℝ => kf f (((1/2 + η : ℝ) : ℂ) + t * I)) := by
  obtain ⟨M, -, hM⟩ := G.kf_bound_left hRH η hη0 hη1
  exact integrable_of_bound _ (G.kf_continuous_line hRH _ (by linarith) (by linarith))
    (1 + η/2) (by linarith) M hM

lemma horiz (hRH : RiemannHypothesis) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1/4) (δ : ℝ) (hδ : 0 < δ)
    (sg : ℝ) (hsg : |sg| = 1) :
    Tendsto (fun T : ℝ => ∫ x in (1/2 + η)..3,
      (fun s => (δ : ℂ) ^ (-s) * kf f s) ((x : ℂ) + (sg * T : ℝ) * I)) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := G.kf_bound_strip hRH η hη0 hη1
  set D := δ ^ (-(1/2 + η)) + δ ^ (-(3:ℝ))
  have hD : 0 ≤ D := by positivity
  have hb : ∀ T : ℝ, 1 ≤ T → ‖∫ x in (1/2 + η)..3,
      (fun s => (δ : ℂ) ^ (-s) * kf f s) ((x : ℂ) + (sg * T : ℝ) * I)‖ ≤
      D * M * (1 + T) ^ (-(η/2)) * |3 - (1/2 + η)| := by
    intro T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have him : ((x : ℂ) + (sg * T : ℝ) * I).im = sg * T := by simp
    have hre : ((x : ℂ) + (sg * T : ℝ) * I).re = x := by simp
    have habs : |sg * T| = T := by rw [abs_mul, hsg, one_mul, abs_of_pos (by linarith)]
    simp only
    rw [norm_mul, norm_dpow δ hδ, hre]
    have h1 := hM ((x : ℂ) + (sg * T : ℝ) * I) (by rw [hre]; linarith [hx.1]) (by rw [hre]; exact hx.2)
      (by rw [him, habs]; exact hT)
    rw [him, habs] at h1
    have h2 := dpow_le δ hδ (1/2 + η) 3 x hx.1.le hx.2
    calc δ ^ (-x) * ‖kf f ((x : ℂ) + (sg * T : ℝ) * I)‖ ≤ D * (M * (1 + T) ^ (-(η/2))) := by
          gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun T : ℝ => D * M * (1 + T) ^ (-(η/2)) * |3 - (1/2 + η)|) atTop (𝓝 0) := by
    have h0 : Tendsto (fun T : ℝ => (1 + T) ^ (-(η/2))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
    simpa using (h0.const_mul (D * M)).mul_const |3 - (1/2 + η)|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact hb T hT

/-- contour shift: discrete sum = residue + left-line integral -/
lemma main_identity (hRH : RiemannHypothesis) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1/4)
    (δ : ℝ) (hδ : 0 < δ) :
    ((∑' k : ℕ, ((k+1 : ℕ).totient : ℝ) * f (δ * (k+1 : ℕ)) : ℝ) : ℂ) =
      (δ : ℂ) ^ (-(2:ℂ)) * mellin (fun x => (f x : ℂ)) 2 * Zi 2 +
      (1 / (2 * Real.pi)) * ∫ t : ℝ, (δ : ℂ) ^ (-(((1/2 + η : ℝ) : ℂ) + t * I)) *
        kf f (((1/2 + η : ℝ) : ℂ) + t * I) := by
  set h : ℂ → ℂ := fun s => (δ : ℂ) ^ (-s) * kf f s with hh
  set q : ℂ → ℂ := fun s => (δ : ℂ) ^ (-s) * mellin (fun x => (f x : ℂ)) s * Zi s with hq
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hdp : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (δ : ℂ) ^ (-s)) s := fun s =>
    differentiableAt_id.neg.const_cpow (Or.inl hδc)
  set A := q 2 with hA
  -- right line identity
  have hR := G.sum_eq_integral δ hδ
  have hRe : (∫ t : ℝ, (δ : ℂ) ^ (-((3:ℂ) + t * I)) *
        mellin (fun x => (f x : ℂ)) ((3:ℂ) + t * I) *
        (riemannZeta ((3:ℂ) + t * I - 1) / riemannZeta ((3:ℂ) + t * I))) =
      ∫ t : ℝ, h (((3:ℝ) : ℂ) + t * I) := by
    apply integral_congr_ae
    filter_upwards with t
    have hs1 : (3:ℂ) + t * I ≠ 1 := by
      intro e; have := congrArg Complex.re e; norm_num at this
    simp only [hh, kf, Zi_eq_of_ne hs1, ofReal_ofNat]
    ring
  rw [hRe] at hR
  have hol : ∀ s : ℂ, (1/2 + η) ≤ s.re → s.re ≤ 3 → s ≠ ((2:ℝ):ℂ) → DifferentiableAt ℂ h s := by
    intro s h1 _ h2
    exact (hdp s).mul (G.kf_differentiableAt hRH s (by linarith) (by simpa using h2))
  have hqd : DifferentiableAt ℂ q 2 :=
    ((hdp 2).mul (G.differentiable 2)).mul (Zi_differentiableAt hRH (by norm_num))
  have near : (h - fun s => A / (s - ((2:ℝ):ℂ))) =O[𝓝[≠] ((2:ℝ):ℂ)] (1 : ℂ → ℂ) := by
    simp only [ofReal_ofNat]
    have ht : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 2) (𝓝[≠] 1) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun s : ℂ => s - 1) (𝓝 2) (𝓝 (2 - 1)) :=
          (continuous_sub_right (1:ℂ)).tendsto 2
        rw [show (2:ℂ) - 1 = 1 by norm_num] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        intro e; apply hs; simp only [mem_singleton_iff] at e ⊢; linear_combination e
    have hz : (fun s : ℂ => riemannZeta (s - 1) - 1 / (s - 2)) =O[𝓝[≠] 2] (fun _ => (1:ℂ)) := by
      have := (tendsto_riemannZeta_sub_one_div.comp ht).isBigO_one ℂ
      refine this.congr_left (fun s => ?_)
      simp only [Function.comp]
      ring_nf
    have hq1 : q =O[𝓝[≠] 2] (fun _ => (1:ℂ)) :=
      (hqd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
    have hsl := (hasDerivAt_iff_tendsto_slope.mp hqd.hasDerivAt).isBigO_one ℂ
    have hm := hq1.mul hz
    simp only [mul_one] at hm
    have hsum := hm.add hsl
    refine (hsum.congr' ?_ (EventuallyEq.refl _ _)).trans (Asymptotics.isBigO_refl _ _)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs2 : s - 2 ≠ 0 := sub_ne_zero.mpr hs
    simp only [Pi.sub_apply, hh, hq, hA, kf, slope_def_field, Pi.one_apply]
    field_simp
    ring
  have intL : Integrable (fun t : ℝ => h (((1/2 + η : ℝ) : ℂ) + t * I)) := by
    refine ((G.kf_int_left hRH η hη0 hη1).norm.const_mul (δ ^ (-(1/2 + η)))).mono' ?_ ?_
    · exact ((Continuous.const_cpow (by fun_prop) (Or.inl hδc)).mul
        (G.kf_continuous_line hRH _ (by linarith) (by linarith))).aestronglyMeasurable
    · filter_upwards with t
      simp only [hh, norm_mul, norm_dpow δ hδ]
      simp
  have intR : Integrable (fun t : ℝ => h (((3 : ℝ) : ℂ) + t * I)) := by
    obtain ⟨M, hM⟩ := G.kf_bound_right
    refine integrable_of_bound _ ((Continuous.const_cpow (by fun_prop) (Or.inl hδc)).mul
        (G.kf_continuous_line hRH 3 (by norm_num) (by norm_num))) 2 (by norm_num)
        (δ ^ (-(3:ℝ)) * M) (fun t _ => ?_)
    simp only [hh, norm_mul, norm_dpow δ hδ]
    have := hM t
    simp only [ofReal_ofNat] at this ⊢
    simp only [add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    rw [mul_assoc]
    gcongr
  have top := G.horiz hRH η hη0 hη1 δ hδ 1 (by simp)
  have bot := G.horiz hRH η hη0 hη1 δ hδ (-1) (by simp)
  have hs := VerjShift.shift h (1/2 + η) 3 2 A (by linarith) (by norm_num) hol near intL intR
    (by refine top.congr (fun T => ?_); congr 1; funext x; simp only [hh]; push_cast; ring_nf)
    (by refine bot.congr (fun T => ?_); congr 1; funext x; simp only [hh]; push_cast; ring_nf)
  rw [hR]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : (∫ t : ℝ, h (((3:ℝ) : ℂ) + t * I)) = 2 * Real.pi * A +
      ∫ t : ℝ, h (((1/2 + η : ℝ) : ℂ) + t * I) := by linear_combination hs
  rw [e, hA, mul_add]
  simp only [hq, hh]
  congr 1
  field_simp

end VerjMellin.Good
end V5b

section V6

open Complex Filter Topology Set MeasureTheory

namespace VerjMellin.Good
open VerjZi
variable {f : ℝ → ℝ} {α β : ℝ} (G : Good f α β)
include G

lemma error_bound (hRH : RiemannHypothesis) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1/4) (y : ℝ)
    (hy : 0 < y) :
    |(∑' k : ℕ, y * ((k+1 : ℕ).totient : ℝ) * f (Real.sqrt y * (k+1 : ℕ))) -
        (6 / Real.pi ^ 2) * (∫ x in Ioi (0:ℝ), x * f x)| ≤
      ((∫ t : ℝ, ‖kf f (((1/2 + η : ℝ) : ℂ) + t * I)‖) / (2 * Real.pi)) *
        y ^ (3/4 - η/2) := by
  set δ := Real.sqrt y with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.mpr hy
  set L := ∫ t : ℝ, ‖kf f (((1/2 + η : ℝ) : ℂ) + t * I)‖
  set J := ∫ t : ℝ, (δ : ℂ) ^ (-(((1/2 + η : ℝ) : ℂ) + t * I)) * kf f (((1/2 + η : ℝ) : ℂ) + t * I)
  have hmain := G.main_identity hRH η hη0 hη1 δ hδ
  have hsum : (∑' k : ℕ, y * ((k+1 : ℕ).totient : ℝ) * f (δ * (k+1 : ℕ))) =
      y * ∑' k : ℕ, ((k+1 : ℕ).totient : ℝ) * f (δ * (k+1 : ℕ)) := by
    rw [← tsum_mul_left]; congr 1; funext k; ring
  rw [hsum]
  -- the residue term
  have hd2 : (δ : ℂ) ^ (-(2:ℂ)) = ((y : ℝ) : ℂ)⁻¹ := by
    rw [cpow_neg, show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, cpow_natCast]
    congr 1
    rw [hδdef]; exact_mod_cast Real.sq_sqrt hy.le
  have hZ2 : Zi 2 = 6 / (Real.pi : ℂ) ^ 2 := by
    rw [Zi_eq_of_ne (by norm_num), riemannZeta_two]; field_simp
  have hres : (y : ℂ) * ((δ : ℂ) ^ (-(2:ℂ)) * mellin (fun x => (f x : ℂ)) 2 * Zi 2) =
      (((6 / Real.pi ^ 2) * (∫ x in Ioi (0:ℝ), x * f x) : ℝ) : ℂ) := by
    rw [hd2, hZ2, G.mellin_two]
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast
    field_simp
  have hcx : (((y * ∑' k : ℕ, ((k+1 : ℕ).totient : ℝ) * f (δ * (k+1 : ℕ))) -
      (6 / Real.pi ^ 2) * (∫ x in Ioi (0:ℝ), x * f x) : ℝ) : ℂ) =
      (y : ℂ) * (1 / (2 * Real.pi)) * J := by
    rw [ofReal_sub, ofReal_mul, hmain, ← hres]; ring
  have hJ : ‖J‖ ≤ δ ^ (-(1/2 + η)) * L := by
    calc ‖J‖ ≤ ∫ t : ℝ, ‖(δ : ℂ) ^ (-(((1/2 + η : ℝ) : ℂ) + t * I)) *
          kf f (((1/2 + η : ℝ) : ℂ) + t * I)‖ := norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, δ ^ (-(1/2 + η)) * ‖kf f (((1/2 + η : ℝ) : ℂ) + t * I)‖ := by
          congr 1; funext t; rw [norm_mul, norm_dpow δ hδ]; simp
      _ = _ := integral_const_mul _ _
  have hpow : y * δ ^ (-(1/2 + η)) = y ^ (3/4 - η/2) := by
    rw [hδdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hy.le]
    conv_lhs => arg 1; rw [← Real.rpow_one y]
    rw [← Real.rpow_add hy]; congr 1; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hcx]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [this, ← hpow]
  calc y * (1 / (2 * Real.pi)) * ‖J‖ ≤ y * (1 / (2 * Real.pi)) * (δ ^ (-(1/2 + η)) * L) := by
        gcongr
    _ = L / (2 * Real.pi) * (y * δ ^ (-(1/2 + η))) := by ring

end VerjMellin.Good

namespace VerjFinal
open VerjMellin

theorem verjovsky_of_RH (hRH : RiemannHypothesis) :
    ∀ r : ℕ∞, 2 ≤ r → ∀ f : ℝ → ℝ, ContDiff ℝ r f → HasCompactSupport f → tsupport f ⊆ Set.Ioi 0 →
      let m (y : ℝ) := ∑' k : ℕ, y * ((k+1).totient : ℝ) * f (Real.sqrt y * (k+1 : ℕ))
      let m₀ := (6 / Real.pi^2) * (∫ x in Set.Ioi (0 : ℝ), x * f x)
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
        (fun y : ℝ => m y - m₀) (fun y : ℝ => y^(3/4-ε)) := by
  intro r hr f hf hcs hts
  dsimp only
  intro ε hε
  obtain ⟨α, β, hα, hαβ, hsub⟩ : ∃ α β : ℝ, 0 < α ∧ α < β ∧ tsupport f ⊆ Ioo α β := by
    by_cases hne : (tsupport f).Nonempty
    · have hK : IsCompact (tsupport f) := hcs
      obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
      obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
      have ha0 : 0 < a := hts ha
      have hab : a ≤ b := isMaxOn_iff.mp hbmax a ha
      refine ⟨a/2, b+1, by linarith, by linarith, fun x hx => ⟨?_, ?_⟩⟩
      · have := isMinOn_iff.mp hamin x hx; simp only [id] at this; linarith
      · have := isMaxOn_iff.mp hbmax x hx; simp only [id] at this; linarith
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨1, 2, by norm_num, by norm_num, by simp [hne]⟩
  have h2 : ContDiff ℝ 2 f := hf.of_le (by
    have h' : ((2:ℕ∞) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := WithTop.coe_le_coe.mpr hr
    exact h')
  have G := Good.of_contDiff hα hαβ h2 hsub
  set η := min ε (1/4) with hηdef
  have hη0 : 0 < η := lt_min hε (by norm_num)
  have hη1 : η ≤ 1/4 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  set L := ∫ t : ℝ, ‖VerjZi.kf f (((1/2 + η : ℝ) : ℂ) + t * I)‖
  have hO : (fun y : ℝ => (∑' k : ℕ, y * ((k+1).totient : ℝ) * f (Real.sqrt y * (k+1 : ℕ))) -
      (6 / Real.pi^2) * (∫ x in Set.Ioi (0 : ℝ), x * f x)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun y : ℝ => y ^ (3/4 - η/2)) := by
    refine Asymptotics.IsBigO.of_bound (L / (2 * Real.pi)) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hy) _)]
    exact G.error_bound hRH η hη0 hη1 y hy
  have ho : (fun y : ℝ => y ^ (3/4 - η/2)) =o[nhdsWithin 0 (Set.Ioi 0)]
      (fun y : ℝ => y ^ (3/4 - ε)) := by
    have hp : 0 < ε - η/2 := by linarith
    have ht : Tendsto (fun y : ℝ => y ^ (ε - η/2)) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (ε - η/2) (Or.inr hp.le)).tendsto
      rw [Real.zero_rpow hp.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h1 := (Asymptotics.isLittleO_one_iff ℝ).mpr ht
    have h2 := h1.mul_isBigO (Asymptotics.isBigO_refl (fun y : ℝ => y ^ (3/4 - ε)) _)
    simp only [one_mul] at h2
    refine h2.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [← Real.rpow_add hy]; congr 1; ring
  exact hO.trans_isLittleO ho

end VerjFinal
end V6

theorem solution :
    ∀ r : ℕ∞, 2 ≤ r → ∀ f : ℝ → ℝ, ContDiff ℝ r f → HasCompactSupport f → tsupport f ⊆ Set.Ioi 0 →
      let m (y : ℝ) := ∑' k : ℕ, y * ((k+1).totient : ℝ) * f (Real.sqrt y * (k+1 : ℕ))
      let m₀ := (6 / Real.pi^2) * (∫ x in Set.Ioi (0 : ℝ), x * f x)
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
        (fun y : ℝ => m y - m₀) (fun y : ℝ => y^(3/4-ε)) :=
  VerjFinal.verjovsky_of_RH riemann_hypothesis
