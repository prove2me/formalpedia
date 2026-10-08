-- Prove2me | solution 1 for DaiWeissFluid.ThreeBuffer.lemma2_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:37:45.904595+00:00
-- url     : https://prove2.me/submissions/e456d363-c433-4e1e-8f79-a906bcf3b7b2

import Mathlib

set_option autoImplicit false

open MeasureTheory in
theorem dwf78713b71_ae_ne_zero : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
  rw [ae_iff]; simp

open MeasureTheory in
theorem dwf78713b71_deriv_nonpos (g : ℝ → ℝ)
    (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t ∂(volume : Measure ℝ),
      0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -ε) :
    ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → deriv g t ≤ 0 := by
  filter_upwards [hdrift] with t ht htpos
  by_cases hd : DifferentiableAt ℝ g t
  · rcases (hg t htpos.le).lt_or_eq with hpos | hzero
    · have := ht htpos hpos (deriv g t) hd.hasDerivAt
      linarith
    · have hmin : IsLocalMin g t := by
        filter_upwards [lt_mem_nhds htpos] with y hy
        rw [← hzero]
        exact hg y hy.le
      exact (hmin.deriv_eq_zero).le
  · rw [deriv_zero_of_not_differentiableAt hd]

open MeasureTheory in
theorem dwf78713b71_antitone (g : ℝ → ℝ)
    (hac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval g a b)
    (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t ∂(volume : Measure ℝ),
      0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -ε) :
    AntitoneOn g (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : (0:ℝ) ≤ a := ha
  have hF := (hac a b ha' hab).integral_deriv_eq_sub
  have hI : ∫ x in a..b, deriv g x ≤ ∫ x in a..b, (0:ℝ) := by
    apply intervalIntegral.integral_mono_ae_restrict hab
      (hac a b ha' hab).intervalIntegrable_deriv intervalIntegrable_const
    have h1 := dwf78713b71_deriv_nonpos g hg ε hε hdrift
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h1,
      ae_restrict_of_ae dwf78713b71_ae_ne_zero] with x hx hx1 hx0
    exact hx1 (lt_of_le_of_ne (le_trans ha' hx.1) (Ne.symm hx0))
  simp at hI
  linarith

open MeasureTheory in
theorem solution (g : ℝ → ℝ)
    (hac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval g a b)
    (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t ∂(volume : Measure ℝ),
      0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -ε) :
    (∀ t, g 0 / ε ≤ t → g t = 0) ∧ AntitoneOn g (Set.Ici 0) := by
  have hanti := dwf78713b71_antitone g hac hg ε hε hdrift
  refine ⟨?_, hanti⟩
  intro t ht
  have hg0 : 0 ≤ g 0 := hg 0 le_rfl
  have hT : 0 ≤ g 0 / ε := div_nonneg hg0 hε.le
  have ht0 : 0 ≤ t := le_trans hT ht
  by_contra hne
  have hpos : 0 < g t := lt_of_le_of_ne (hg t ht0) (Ne.symm hne)
  have hall : ∀ s, 0 ≤ s → s ≤ t → 0 < g s := fun s hs hst =>
    lt_of_lt_of_le hpos (hanti (Set.mem_Ici.mpr hs) (Set.mem_Ici.mpr ht0) hst)
  have hAC := hac 0 t le_rfl ht0
  have hF := hAC.integral_deriv_eq_sub
  have hI : ∫ x in (0:ℝ)..t, deriv g x ≤ ∫ x in (0:ℝ)..t, (-ε) := by
    apply intervalIntegral.integral_mono_ae_restrict ht0
      hAC.intervalIntegrable_deriv intervalIntegrable_const
    have hd := hAC.ae_differentiableAt
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hdrift,
      ae_restrict_of_ae hd, ae_restrict_of_ae dwf78713b71_ae_ne_zero] with x hx hx1 hx2 hx0
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hxu : x ∈ Set.uIcc (0:ℝ) t := by
      rw [Set.uIcc_of_le ht0]; exact hx
    exact hx1 hxpos (hall x hx.1 hx.2) _ (hx2 hxu).hasDerivAt
  simp at hI
  have hεt : g 0 ≤ ε * t := by
    have := (div_le_iff₀ hε).mp ht
    linarith
  linarith
