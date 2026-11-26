-- Prove2me | solution 1 for FiniteEnergyPlane.injOn_leafSweep
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T21:51:20.680777+00:00
-- url     : https://prove2.me/submissions/40336d8a-adff-43e6-93f9-a42472ffc386

import Definitions.Def_FiniteEnergyPlane_SpanningDisk
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_exitTime_of_leavesRadiateFrom
import Theorems.Thm_FiniteEnergyPlane_flow_add_apply
import Theorems.Thm_FiniteEnergyPlane_injOn_Ico_of_hasLoopWind_one
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_continuousOn_family
import Theorems.Thm_FiniteEnergyPlane_injOn_ball_of_hasStrictFDerivAt



/-! Child G of P c5a21fab: `injOn_leafSweep` (sketch over E, D, W, 6d46a231, 4c646f2d). -/

namespace FiniteEnergyPlane

open Metric Set Filter Topology
open scoped ContDiff

theorem olpg_liou_add (x v w : V 1) : liouville x (v + w) = liouville x v + liouville x w := by
  simp only [liouville, omega0, dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring

theorem olpg_liou_smul (x v : V 1) (a : ℝ) : liouville x (a • v) = a * liouville x v := by
  simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem olpg_liou_eq (e : ℂ → V 1) (z w : ℂ) :
    liouville (e z) (fderiv ℝ e z w) = (charField e z).re * w.im - (charField e z).im * w.re := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, olpg_liou_add, olpg_liou_smul, olpg_liou_smul]
  simp only [charField, ds, dt]
  ring

theorem olpg_apply (L : ℂ →L[ℝ] ℂ) (a : ℂ) : L a = a.re • L 1 + a.im • L Complex.I := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [ha]
  rw [map_add, map_smul, map_smul]

theorem olpg_fderiv_snd (Ψ : ℝ × ℂ → ℂ) (hΨ : Differentiable ℝ Ψ) (τ : ℝ) (z v : ℂ) :
    fderiv ℝ (fun y => Ψ (τ, y)) z v = fderiv ℝ Ψ (τ, z) (0, v) := by
  have h : HasFDerivAt (fun y => Ψ (τ, y))
      ((fderiv ℝ Ψ (τ, z)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) z :=
    (hΨ (τ, z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right τ z)
  rw [h.fderiv]; rfl

theorem olpg_fderiv_fst (Ψ : ℝ × ℂ → ℂ) (hΨ : Differentiable ℝ Ψ) (τ : ℝ) (z : ℂ) (d : ℂ)
    (hd : HasDerivAt (fun s => Ψ (s, z)) d τ) : fderiv ℝ Ψ (τ, z) (1, 0) = d := by
  have h1 : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : ℂ)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ z)
  exact ((hΨ (τ, z)).hasFDerivAt.comp_hasDerivAt τ h1).unique hd

theorem olpg_norm_add_le (r s : ℝ) : ‖(r : ℂ) + s * Complex.I‖ ≤ |r| + |s| := by
  refine (norm_add_le _ _).trans ?_
  simp [Complex.norm_real]

theorem injOn_leafSweep_aux (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z₀ : ℂ)
    (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hV : charField e z₀ = 0) (hL : LeavesRadiateFrom e z₀)
    (hS : ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z)))
    (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (hXK : HasCompactSupport X)
    (hXV : ∀ z ∈ ball (0 : ℂ) 2, X z = charField e z)
    (ψ : ℝ → ℂ → ℂ) (hψ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ψ p.1 p.2)) (hψ0 : ∀ y, ψ 0 y = y)
    (hψd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t)
    (c : ℝ → ℂ) (hc : ContDiff ℝ 1 c) (hcA : ∀ t, c t ∈ closedBall (0 : ℂ) 1)
    (hw : HasLoopWind (fun t => c t - z₀) 1)
    (htr : ∀ t, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) ≠ 0) :
    InjOn (fun p : ℂ => ψ p.re (c p.im)) {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1} := by
  have hψc : Continuous (fun p : ℝ × ℂ => ψ p.1 p.2) := hψ.continuous
  obtain ⟨b, hbc, hb⟩ := exists_exitTime_of_leavesRadiateFrom e he z₀ hz₀ hV hL hS X hX hXK hXV ψ
    hψc hψ0 hψd
  have hgrp : ∀ s r y, ψ s (ψ r y) = ψ (s + r) y := flow_add_apply X hX hXK ψ hψ0 hψd
  set D := closedBall (0 : ℂ) 1 \ {z₀} with hD
  have hcz : ∀ t, c t ≠ z₀ := fun t h => hw.2.2.1 t (by simp [h])
  have hcD : ∀ t, c t ∈ D := fun t => ⟨hcA t, hcz t⟩
  have hcc : Continuous c := hc.continuous
  have hbcc : Continuous (fun t => b (c t)) :=
    hbc.comp_continuous hcc hcD
  have hcper : Function.Periodic c 1 := fun t => by
    have := hw.2.1 t; simpa using this
  -- the exit time is the only time on the circle; it is shifted along orbits
  have hsph : ∀ y ∈ D, ∀ s, ψ s y ∈ sphere (0 : ℂ) 1 → s = b y := by
    intro y hy s hs
    obtain ⟨-, hin, -, hout, -⟩ := hb y hy.1 hy.2
    rcases lt_trichotomy s (b y) with h | h | h
    · have := mem_ball_zero_iff.1 (hin s h); rw [mem_sphere_zero_iff_norm] at hs; linarith
    · exact h
    · exact absurd (sphere_subset_closedBall hs) (hout s h)
  set Ex : ℂ → ℂ := fun y => ψ (b y) y with hExdef
  have hExorb : ∀ y ∈ D, ∀ r, ψ r y ∈ D → Ex (ψ r y) = Ex y := by
    intro y hy r hry
    have h1 : ψ (b y - r) (ψ r y) = ψ (b y) y := by rw [hgrp]; ring_nf
    have hb' : b (ψ r y) = b y - r :=
      (hsph _ hry _ (by rw [h1]; exact (hb y hy.1 hy.2).2.2.1)).symm
    simp only [hExdef, hb', h1]
  -- the exit loop
  set γ : ℝ → ℂ := fun t => Ex (c t) with hγdef
  have hγc : Continuous γ := hψc.comp (hbcc.prodMk hcc)
  have hγ1 : ∀ t, ‖γ t‖ = 1 := fun t =>
    mem_sphere_zero_iff_norm.1 (hb (c t) (hcA t) (hcz t)).2.2.1
  have hγper : Function.Periodic γ 1 := fun t => by simp only [hγdef, hcper t]
  -- winding of the exit loop
  have hwγ : HasLoopWind γ 1 := by
    set F : ℝ → ℝ → ℂ := fun l t => ψ (l * b (c t)) (c t) - z₀ with hF
    have hFc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 1 ×ˢ univ) :=
      (Continuous.sub (hψc.comp ((continuous_fst.mul (hbcc.comp continuous_snd)).prodMk
        (hcc.comp continuous_snd))) continuous_const).continuousOn
    have hFper : ∀ l ∈ Icc (0 : ℝ) 1, Function.Periodic (F l) 1 := fun l _ t => by
      simp only [hF, hcper t]
    have hF0 : ∀ l ∈ Icc (0 : ℝ) 1, ∀ t, F l t ≠ 0 := fun l _ t => by
      simp only [hF]; exact sub_ne_zero.2 ((hb (c t) (hcA t) (hcz t)).2.2.2.2.2 _)
    have hFa : HasLoopWind (F 0) 1 := by
      have : F 0 = fun t => c t - z₀ := by funext t; simp [hF, hψ0]
      rw [this]; exact hw
    have h1 := hasLoopWind_of_continuousOn_family F hFc hFper hF0 hFa 1 ⟨zero_le_one, le_rfl⟩
    have hF1 : F 1 = fun t => γ t - z₀ := by funext t; simp [hF, hγdef, hExdef]
    rw [hF1] at h1
    set H : ℝ → ℝ → ℂ := fun l t => γ t - ((1 - l : ℝ) : ℂ) * z₀ with hH
    have hHc : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ univ) :=
      (Continuous.sub (hγc.comp continuous_snd)
        ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).mul
          continuous_const)).continuousOn
    have hHper : ∀ l ∈ Icc (0 : ℝ) 1, Function.Periodic (H l) 1 := fun l _ t => by
      simp only [hH, hγper t]
    have hH0 : ∀ l ∈ Icc (0 : ℝ) 1, ∀ t, H l t ≠ 0 := by
      intro l hl t h
      have h' : γ t = ((1 - l : ℝ) : ℂ) * z₀ := sub_eq_zero.1 h
      have hn := congrArg norm h'
      rw [hγ1 t, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hl.2])] at hn
      have hz := mem_ball_zero_iff.1 hz₀
      have : (1 - l) * ‖z₀‖ < 1 := by
        have : (1 - l) * ‖z₀‖ ≤ ‖z₀‖ := by
          have := norm_nonneg z₀; nlinarith [hl.1]
        linarith
      linarith
    have hHa : HasLoopWind (H 0) 1 := by
      have : H 0 = fun t => γ t - z₀ := by funext t; simp [hH]
      rw [this]; exact h1
    have h2 := hasLoopWind_of_continuousOn_family H hHc hHper hH0 hHa 1 ⟨zero_le_one, le_rfl⟩
    have hH1 : H 1 = γ := by funext t; simp [hH]
    rwa [hH1] at h2
  -- the sweep map and its derivative
  set Ψ : ℝ × ℂ → ℂ := fun p => ψ p.1 p.2 with hΨdef
  have hΨd : Differentiable ℝ Ψ := hψ.differentiable (by simp)
  have hcd : ∀ t, HasDerivAt c (deriv c t) t := fun t =>
    ((hc.differentiable (by norm_num)) t).hasDerivAt
  set Φ : ℂ → ℂ := fun p => ψ p.re (c p.im) with hΦdef
  let L : ℂ → ℂ →L[ℝ] ℝ × ℂ := fun p =>
    Complex.reCLM.prod ((ContinuousLinearMap.toSpanSingleton ℝ (deriv c p.im)).comp Complex.imCLM)
  have hLd : ∀ p : ℂ, HasFDerivAt (fun q : ℂ => (q.re, c q.im)) (L p) p := fun p =>
    Complex.reCLM.hasFDerivAt.prodMk ((hcd p.im).hasFDerivAt.comp p Complex.imCLM.hasFDerivAt)
  set Φ' : ℂ → ℂ →L[ℝ] ℂ := fun p => (fderiv ℝ Ψ (p.re, c p.im)).comp (L p) with hΦ'def
  have hΦ : ∀ p, HasFDerivAt Φ (Φ' p) p := fun p => by
    have := HasFDerivAt.comp p (g := Ψ) (hΨd (p.re, c p.im)).hasFDerivAt (hLd p)
    exact this
  have hΦcd : ContDiff ℝ 1 Φ :=
    (hψ.of_le (by simp)).comp (Complex.reCLM.contDiff.prodMk (hc.comp Complex.imCLM.contDiff))
  have hΦ'1 : ∀ p, Φ' p 1 = X (Φ p) := by
    intro p
    have : Φ' p 1 = fderiv ℝ Ψ (p.re, c p.im) (1, 0) := by simp [hΦ'def, L]
    rw [this]
    exact olpg_fderiv_fst Ψ hΨd p.re (c p.im) _ (hψd p.re (c p.im))
  have hψ0' : ψ 0 = id := funext hψ0
  have hΦ'I : ∀ t : ℝ, Φ' (t * Complex.I) Complex.I = deriv c t := by
    intro t
    have hre : ((t : ℂ) * Complex.I).re = 0 := by simp
    have him : ((t : ℂ) * Complex.I).im = t := by simp
    have : Φ' (t * Complex.I) Complex.I =
        fderiv ℝ Ψ (((t : ℂ) * Complex.I).re, c ((t : ℂ) * Complex.I).im)
          (0, deriv c ((t : ℂ) * Complex.I).im) := by simp [hΦ'def, L]
    rw [this, ← olpg_fderiv_snd Ψ hΨd, hre, him]
    simp only [hΨdef, hψ0', id_eq, fderiv_id', ContinuousLinearMap.id_apply]
  -- local injectivity of the exit loop
  have hloc : ∀ t₀, ∃ ε > 0, InjOn γ (ball t₀ ε) := by
    intro t₀
    set p₀ : ℂ := t₀ * Complex.I
    have hΦ0 : Φ p₀ = c t₀ := by simp [p₀, hΦdef, hψ0]
    have hstrict : HasStrictFDerivAt Φ (Φ' p₀) p₀ := by
      have := (hΦcd.contDiffAt (x := p₀)).hasStrictFDerivAt (by norm_num)
      rwa [(hΦ p₀).fderiv] at this
    have hXc : X (c t₀) = charField e (c t₀) :=
      hXV _ (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (hcA t₀)) (by norm_num)))
    have hω : (X (c t₀)).re * (deriv c t₀).im - (X (c t₀)).im * (deriv c t₀).re ≠ 0 := by
      rw [hXc, ← olpg_liou_eq]; exact htr t₀
    have hker : ∀ v, Φ' p₀ v = 0 → v = 0 := by
      intro v hv'
      rw [olpg_apply, hΦ'1, hΦ0, hΦ'I] at hv'
      have hre := congrArg Complex.re hv'
      have him := congrArg Complex.im hv'
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
        Complex.zero_re, Complex.zero_im] at hre him
      have h1 : v.im * ((X (c t₀)).re * (deriv c t₀).im - (X (c t₀)).im * (deriv c t₀).re) = 0 := by
        linear_combination (X (c t₀)).re * him - (X (c t₀)).im * hre
      have h2 : v.re * ((X (c t₀)).re * (deriv c t₀).im - (X (c t₀)).im * (deriv c t₀).re) = 0 := by
        linear_combination (deriv c t₀).im * hre - (deriv c t₀).re * him
      have hvi := (mul_eq_zero.1 h1).resolve_right hω
      have hvr := (mul_eq_zero.1 h2).resolve_right hω
      exact Complex.ext hvr hvi
    have hinj' : Function.Injective (Φ' p₀) := fun v w h =>
      sub_eq_zero.1 (hker _ (by rw [map_sub, h, sub_self]))
    obtain ⟨δ, hδ, hΦinj⟩ := injOn_ball_of_hasStrictFDerivAt hstrict hinj'
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.continuous_iff.1 hbcc t₀ (δ / 4) (by linarith)
    refine ⟨min ε₁ (δ / 4), lt_min hε₁ (by linarith), fun t₁ ht₁ t₂ ht₂ heq => ?_⟩
    have ht₁' : dist t₁ t₀ < ε₁ := lt_of_lt_of_le (mem_ball.1 ht₁) (min_le_left _ _)
    have ht₂' : dist t₂ t₀ < ε₁ := lt_of_lt_of_le (mem_ball.1 ht₂) (min_le_left _ _)
    have ht₁'' : |t₁ - t₀| < δ / 4 := by
      rw [← Real.dist_eq]; exact lt_of_lt_of_le (mem_ball.1 ht₁) (min_le_right _ _)
    have ht₂'' : |t₂ - t₀| < δ / 4 := by
      rw [← Real.dist_eq]; exact lt_of_lt_of_le (mem_ball.1 ht₂) (min_le_right _ _)
    have hb1 := hb₁ t₁ ht₁'
    have hb2 := hb₁ t₂ ht₂'
    rw [Real.dist_eq] at hb1 hb2
    set r := b (c t₁) - b (c t₂) with hr
    have hr' : |r| < δ / 2 := by
      have : |r| ≤ |b (c t₁) - b (c t₀)| + |b (c t₂) - b (c t₀)| := by
        rw [hr]
        calc |b (c t₁) - b (c t₂)| = |(b (c t₁) - b (c t₀)) - (b (c t₂) - b (c t₀))| := by ring_nf
          _ ≤ _ := abs_sub _ _
      linarith
    -- one point reaches the other along the flow
    have hreach : ψ r (c t₁) = c t₂ := by
      have h := congrArg (ψ (-b (c t₂))) heq
      simp only [hγdef, hExdef, hgrp, neg_add_cancel, hψ0] at h
      rw [← h]; congr 1; rw [hr]; ring
    have hq₁ : (r : ℂ) + t₁ * Complex.I ∈ ball p₀ δ := by
      rw [mem_ball, dist_eq_norm]
      have : (r : ℂ) + t₁ * Complex.I - p₀ = (r : ℂ) + ((t₁ - t₀ : ℝ) : ℂ) * Complex.I := by
        simp [p₀]; ring
      rw [this]
      exact lt_of_le_of_lt (olpg_norm_add_le _ _) (by linarith)
    have hq₂ : ((0 : ℝ) : ℂ) + t₂ * Complex.I ∈ ball p₀ δ := by
      rw [mem_ball, dist_eq_norm]
      have : ((0 : ℝ) : ℂ) + t₂ * Complex.I - p₀ = ((0 : ℝ) : ℂ) + ((t₂ - t₀ : ℝ) : ℂ) * Complex.I := by
        simp [p₀]; ring
      rw [this]
      exact lt_of_le_of_lt (olpg_norm_add_le _ _) (by simp; linarith)
    have hval : Φ ((r : ℂ) + t₁ * Complex.I) = Φ (((0 : ℝ) : ℂ) + t₂ * Complex.I) := by
      simp only [hΦdef, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
        zero_add, add_zero, zero_mul]
      rw [hψ0, hreach]
    have := congrArg Complex.im (hΦinj hq₁ hq₂ hval)
    simpa using this
  have hγinj := injOn_Ico_of_hasLoopWind_one γ hwγ hγ1 hloc
  -- injectivity of the sweep
  intro p hp p' hp' heq
  set τ := p.re; set t := p.im; set τ' := p'.re; set t' := p'.im
  have hreach : c t' = ψ (τ - τ') (c t) := by
    have h := congrArg (ψ (-τ')) heq
    rw [hgrp, hgrp, neg_add_cancel, hψ0] at h
    rw [← h]; congr 1; ring
  have htt : t = t' := by
    refine hγinj hp.2 hp'.2 ?_
    simp only [hγdef]
    rw [hreach, hExorb (c t) (hcD t) (τ - τ') (hreach ▸ hcD t')]
  have hper : ψ (τ - τ') (c t) = c t := by rw [← hreach, ← htt]
  have hττ : τ = τ' := by
    by_contra hne
    set d := -|τ - τ'| with hd
    have hdneg : d < 0 := by
      have : 0 < |τ - τ'| := abs_pos.2 (sub_ne_zero.2 hne); linarith
    have hpd : ψ d (c t) = c t := by
      rcases le_or_gt 0 (τ - τ') with h | h
      · have : d = -(τ - τ') := by rw [hd, abs_of_nonneg h]
        rw [this]
        have := congrArg (ψ (-(τ - τ'))) hper
        rw [hgrp, neg_add_cancel, hψ0] at this
        exact this.symm
      · have : d = τ - τ' := by rw [hd, abs_of_neg h, neg_neg]
        rw [this]; exact hper
    have hn : ∀ n : ℕ, ψ (n * d) (c t) = c t := by
      intro n
      induction n with
      | zero => simp [hψ0]
      | succ n ih =>
        have : ((n + 1 : ℕ) : ℝ) * d = n * d + d := by push_cast; ring
        rw [this, ← hgrp, hpd, ih]
    have htend := (hb (c t) (hcA t) (hcz t)).2.2.2.2.1
    have hseq : Tendsto (fun n : ℕ => (n : ℝ) * d) atTop atBot :=
      tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hdneg
    have := htend.comp hseq
    have hconst : Tendsto (fun n : ℕ => ψ (n * d) (c t)) atTop (𝓝 (c t)) := by
      simp only [hn]; exact tendsto_const_nhds
    exact hcz t (tendsto_nhds_unique hconst this)
  exact Complex.ext hττ htt

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Set
open scoped ContDiff

theorem solution (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z₀ : ℂ)
    (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hV : charField e z₀ = 0) (hL : LeavesRadiateFrom e z₀)
    (hS : ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z)))
    (X : ℂ → ℂ) (hX : ContDiff ℝ ∞ X) (hXK : HasCompactSupport X)
    (hXV : ∀ z ∈ ball (0 : ℂ) 2, X z = charField e z)
    (ψ : ℝ → ℂ → ℂ) (hψ : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ψ p.1 p.2)) (hψ0 : ∀ y, ψ 0 y = y)
    (hψd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t)
    (c : ℝ → ℂ) (hc : ContDiff ℝ 1 c) (hcA : ∀ t, c t ∈ closedBall (0 : ℂ) 1)
    (hw : HasLoopWind (fun t => c t - z₀) 1)
    (htr : ∀ t, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) ≠ 0) :
    InjOn (fun p : ℂ => ψ p.re (c p.im)) {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1} :=
  injOn_leafSweep_aux e he z₀ hz₀ hV hL hS X hX hXK hXV ψ hψ hψ0 hψd c hc hcA hw htr
