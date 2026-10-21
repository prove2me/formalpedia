-- Prove2me | solution 1 for CrowdContest.Pooling.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:22:37.49358+00:00
-- url     : https://prove2.me/submissions/3db6745e-3e36-4dc0-9d3e-0ecf2b676340

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

set_option autoImplicit false
open MeasureTheory CrowdContest.Pooling Asymptotics

theorem cc_hd (C : ℝ → ℝ) (hC : IsCost C) (x : ℝ) (hx : 0 < x) : HasDerivAt C (deriv C x) x :=
  ((hC.2.1.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt

theorem cc_sm (C : ℝ → ℝ) (hC : IsCost C) : StrictMonoOn C (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hC.1
  intro x hx
  rw [interior_Ici] at hx
  exact (hC.2.2 x hx).1

theorem cc_sc (C : ℝ → ℝ) (hC : IsCost C) : StrictConvexOn ℝ (Set.Ici 0) C := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0) hC.1
  intro x hx
  rw [interior_Ici] at hx
  simpa using (hC.2.2 x hx).2

theorem cc_tangent (C : ℝ → ℝ) (hC : IsCost C) (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) :
    C x + deriv C x * (y - x) ≤ C y := by
  have hcv : ConvexOn ℝ (Set.Ici 0) C := (cc_sc C hC).convexOn
  have hxm : x ∈ Set.Ici (0:ℝ) := le_of_lt hx
  rcases lt_trichotomy x y with h | h | h
  · have := hcv.le_slope_of_hasDerivAt hxm hy h (cc_hd C hC x hx)
    rw [slope_def_field] at this
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hcv.slope_le_of_hasDerivAt hy hxm h (cc_hd C hC x hx)
    rw [slope_def_field] at this
    rw [div_le_iff₀ (by linarith)] at this
    linarith

theorem cc_attain (C₁ C₂ : ℝ → ℝ) (h1 : ContinuousOn C₁ (Set.Ici 0))
    (h2 : ContinuousOn C₂ (Set.Ici 0)) (e : ℝ) (he : 0 ≤ e) :
    ∃ t, t ∈ Set.Icc 0 e ∧ aggCost C₁ C₂ e = C₁ t + C₂ (e - t) ∧
      ∀ u ∈ Set.Icc 0 e, C₁ t + C₂ (e - t) ≤ C₁ u + C₂ (e - u) := by
  have hcont : ContinuousOn (fun u => C₁ u + C₂ (e - u)) (Set.Icc 0 e) := by
    apply ContinuousOn.add (h1.mono (fun u hu => hu.1))
    refine h2.comp (continuousOn_const.sub continuousOn_id) ?_
    intro u hu
    simp only [Set.mem_Ici]
    linarith [hu.2]
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 he) hcont
  refine ⟨t, ht, ?_, fun u hu => hmin hu⟩
  apply IsLeast.csInf_eq
  refine ⟨⟨t, e - t, ht.1, by linarith [ht.2], by ring, rfl⟩, ?_⟩
  rintro c ⟨a, b, ha, hb, hab, rfl⟩
  have hb' : b = e - a := by linarith
  subst hb'
  exact hmin ⟨ha, by linarith⟩

theorem solution (C₁ C₂ : ℝ → ℝ) (hC₁ : IsCost C₁) (hC₂ : IsCost C₂) :
    StrictMonoOn (aggCost C₁ C₂) (Set.Ici 0) ∧
      StrictConvexOn ℝ (Set.Ici 0) (aggCost C₁ C₂) ∧
      ∀ e₁ e₂, 0 < e₁ → 0 < e₂ → aggCost C₁ C₂ (e₁ + e₂) = C₁ e₁ + C₂ e₂ →
        HasDerivAt (aggCost C₁ C₂) (deriv C₁ e₁) (e₁ + e₂) ∧ deriv C₁ e₁ = deriv C₂ e₂ := by
  have m1 := cc_sm C₁ hC₁
  have m2 := cc_sm C₂ hC₂
  have s1 := cc_sc C₁ hC₁
  have s2 := cc_sc C₂ hC₂
  refine ⟨?_, ?_, ?_⟩
  · -- strictly increasing
    intro e he e' he' hlt
    simp only [Set.mem_Ici] at he he'
    obtain ⟨t', ht', heq', -⟩ := cc_attain C₁ C₂ hC₁.1 hC₂.1 e' he'
    obtain ⟨t, ht, heq, hmin⟩ := cc_attain C₁ C₂ hC₁.1 hC₂.1 e he
    rcases le_or_gt t' e with h | h
    · have := hmin t' ⟨ht'.1, h⟩
      have h3 : C₂ (e - t') < C₂ (e' - t') :=
        m2 (by simp only [Set.mem_Ici]; linarith) (by simp only [Set.mem_Ici]; linarith [ht'.2])
          (by linarith)
      linarith
    · have := hmin e ⟨he, le_rfl⟩
      have h3 : C₁ e < C₁ t' := m1 (by simpa using he) (by simpa using ht'.1) h
      have h4 : C₂ 0 ≤ C₂ (e' - t') := m2.monotoneOn (by simp) (by simp only [Set.mem_Ici]; linarith [ht'.2]) (by linarith [ht'.2])
      rw [sub_self] at this
      linarith
  · -- strictly convex
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    simp only [Set.mem_Ici] at hx hy
    simp only [smul_eq_mul]
    obtain ⟨tx, htx, hex, -⟩ := cc_attain C₁ C₂ hC₁.1 hC₂.1 x hx
    obtain ⟨ty, hty, hey, -⟩ := cc_attain C₁ C₂ hC₁.1 hC₂.1 y hy
    have hz : 0 ≤ a * x + b * y := by positivity
    obtain ⟨t, ht, hez, hmin⟩ := cc_attain C₁ C₂ hC₁.1 hC₂.1 _ hz
    have hu : a * tx + b * ty ∈ Set.Icc 0 (a * x + b * y) :=
      ⟨by have := htx.1; have := hty.1; positivity, by nlinarith [htx.2, hty.2]⟩
    have hle : aggCost C₁ C₂ (a * x + b * y) ≤
        C₁ (a * tx + b * ty) + C₂ (a * (x - tx) + b * (y - ty)) := by
      have e1 : a * x + b * y - (a * tx + b * ty) = a * (x - tx) + b * (y - ty) := by ring
      have := hmin _ hu
      rw [e1] at this
      rw [hez]; exact this
    rw [hex, hey]
    have hx2 : x - tx ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith [htx.2]
    have hy2 : y - ty ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith [hty.2]
    by_cases htt : tx = ty
    · have hxx : x - tx ≠ y - ty := by intro h; apply hxy; linarith
      have := s2.2 hx2 hy2 hxx ha hb hab
      simp only [smul_eq_mul] at this
      subst htt
      have h1 : C₁ (a * tx + b * tx) = a * C₁ tx + b * C₁ tx := by
        have : a * tx + b * tx = tx := by rw [← add_mul, hab, one_mul]
        rw [this]; linear_combination (-(C₁ tx)) * hab
      nlinarith
    · have := s1.2 (show tx ∈ Set.Ici (0:ℝ) from htx.1) (show ty ∈ Set.Ici (0:ℝ) from hty.1) htt ha hb hab
      simp only [smul_eq_mul] at this
      have h2 := s2.convexOn.2 hx2 hy2 ha.le hb.le hab
      simp only [smul_eq_mul] at h2
      linarith
  · -- derivative
    intro e₁ e₂ h1 h2 hopt
    set e := e₁ + e₂ with he
    have he0 : 0 < e := by linarith
    obtain ⟨t0, ht0, heq0, hmin0⟩ := cc_attain C₁ C₂ hC₁.1 hC₂.1 e he0.le
    -- first order condition
    have hFOC : deriv C₁ e₁ = deriv C₂ e₂ := by
      have hg : HasDerivAt (fun t => C₁ t + C₂ (e - t)) (deriv C₁ e₁ - deriv C₂ e₂) e₁ := by
        have h3 : HasDerivAt (fun t : ℝ => e - t) (-1) e₁ := by
          simpa using (hasDerivAt_id e₁).const_sub e
        have h4 : HasDerivAt C₂ (deriv C₂ e₂) (e - e₁) := by
          have : e - e₁ = e₂ := by rw [he]; ring
          rw [this]; exact cc_hd C₂ hC₂ e₂ h2
        have := (cc_hd C₁ hC₁ e₁ h1).add (h4.comp e₁ h3)
        exact this.congr_deriv (by ring)
      have hlm : IsLocalMin (fun t => C₁ t + C₂ (e - t)) e₁ := by
        filter_upwards [Ioo_mem_nhds h1 (show e₁ < e by linarith)] with t ht
        have := hmin0 t ⟨ht.1.le, ht.2.le⟩
        have h5 : e - e₁ = e₂ := by rw [he]; ring
        have h6 : C₁ e₁ + C₂ (e - e₁) = aggCost C₁ C₂ e := by rw [h5]; exact hopt.symm
        show C₁ e₁ + C₂ (e - e₁) ≤ C₁ t + C₂ (e - t)
        linarith [heq0, ht0.1]
      have := hlm.hasDerivAt_eq_zero hg
      linarith
    refine ⟨?_, hFOC⟩
    set lam := deriv C₁ e₁ with hlam
    have hlow : ∀ h, 0 ≤ e + h → aggCost C₁ C₂ e + lam * h ≤ aggCost C₁ C₂ (e + h) := by
      intro h hh
      obtain ⟨t, ht, heq, -⟩ := cc_attain C₁ C₂ hC₁.1 hC₂.1 (e + h) hh
      have a1 := cc_tangent C₁ hC₁ e₁ t h1 ht.1
      have a2 := cc_tangent C₂ hC₂ e₂ (e + h - t) h2 (by linarith [ht.2])
      rw [← hFOC] at a2
      rw [heq, hopt]
      have : lam * (t - e₁) + lam * (e + h - t - e₂) = lam * h := by rw [he]; ring
      nlinarith
    have hup : ∀ h, 0 ≤ e₁ + h → aggCost C₁ C₂ (e + h) ≤ C₁ (e₁ + h) + C₂ e₂ := by
      intro h hh
      have hh2 : 0 ≤ e + h := by rw [he]; linarith
      obtain ⟨t, ht, heq, hmin⟩ := cc_attain C₁ C₂ hC₁.1 hC₂.1 (e + h) hh2
      have := hmin (e₁ + h) ⟨hh, by rw [he]; linarith⟩
      have h7 : e + h - (e₁ + h) = e₂ := by rw [he]; ring
      rw [h7] at this
      linarith
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hρ := (hasDerivAt_iff_isLittleO_nhds_zero.1 (cc_hd C₁ hC₁ e₁ h1))
    refine IsBigO.trans_isLittleO ?_ hρ
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Ioo_mem_nhds (show -e₁ < 0 by linarith) h1] with h hh
    have l1 := hlow h (by rw [he]; linarith [hh.1])
    have u1 := hup h (by linarith [hh.1])
    have hopt' : aggCost C₁ C₂ e = C₁ e₁ + C₂ e₂ := hopt
    simp only [smul_eq_mul, Real.norm_eq_abs, one_mul]
    have hφ : 0 ≤ aggCost C₁ C₂ (e + h) - aggCost C₁ C₂ e - h * lam := by linarith
    have hφρ : aggCost C₁ C₂ (e + h) - aggCost C₁ C₂ e - h * lam ≤ C₁ (e₁ + h) - C₁ e₁ - h * lam := by
      linarith
    rw [abs_of_nonneg hφ, abs_of_nonneg (hφ.trans hφρ)]; exact hφρ
