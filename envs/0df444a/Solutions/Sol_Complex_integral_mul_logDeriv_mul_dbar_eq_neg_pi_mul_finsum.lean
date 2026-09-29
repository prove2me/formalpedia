-- Prove2me | solution 1 for Complex.integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/62ad73c0-e254-5fb1-ba7c-0b2a7dc27cd6

import Mathlib
import Theorems.Thm_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum

noncomputable section

p2m_open "MeasureTheory Complex P2MW.S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum.Complex Filter Set"
open scoped Topology Real

namespace Complex
p2m_export "Complex" "I integral_mul_dbar_eq_neg_pi_mul_finsum_residue"
namespace LogDerivStokes
p2m_open "Complex"

theorem eventually_nhdsNE_eventually_nhds {z : ℂ} {P : ℂ → Prop} (h : ∀ᶠ w in 𝓝[≠] z, P w) :
    ∀ᶠ w in 𝓝[≠] z, ∀ᶠ u in 𝓝 w, P u := by
  rw [eventually_nhdsWithin_iff] at h ⊢
  filter_upwards [h.eventually_nhds] with w hw hwz
  have hne : ∀ᶠ u in 𝓝 w, u ≠ z := isOpen_ne.eventually_mem hwz
  filter_upwards [hw, hne] with u hu hune using hu hune

theorem deriv_zpow_mul_div {G : ℂ → ℂ} {a z : ℂ} (n : ℤ) (hza : z ≠ a)
    (hG : DifferentiableAt ℂ G z) (hG0 : G z ≠ 0) :
    deriv (fun w => (w - a) ^ n * G w) z / ((z - a) ^ n * G z) =
      (n : ℂ) / (z - a) + deriv G z / G z := by
  have hsub : z - a ≠ 0 := sub_ne_zero.2 hza
  have h1 : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1) * 1) z := by
    have := (hasDerivAt_zpow n (z - a) (Or.inl hsub)).comp z ((hasDerivAt_id z).sub_const a)
    exact this
  have h2 : HasDerivAt (fun w : ℂ => (w - a) ^ n * G w)
      ((n : ℂ) * (z - a) ^ (n - 1) * 1 * G z + (z - a) ^ n * deriv G z) z :=
    h1.mul hG.hasDerivAt
  rw [h2.deriv, zpow_sub_one₀ hsub]
  have hpow : (z - a) ^ n ≠ 0 := zpow_ne_zero n hsub
  field_simp

theorem analyticAt_dslope {E : ℂ → ℂ} {a : ℂ} (hE : AnalyticAt ℂ E a) :
    AnalyticAt ℂ (dslope E a) a := by
  obtain ⟨p, hp⟩ := hE
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

theorem hloc_logDeriv {F E : ℂ → ℂ} {a : ℂ} (hF : MeromorphicAt F a) {n : ℤ}
    (hn : meromorphicOrderAt F a = (n : WithTop ℤ)) (hE : AnalyticAt ℂ E a) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, E z * (deriv F z / F z) = (n : ℂ) * E a / (z - a) + g z := by
  obtain ⟨G, hGan, hG0, hev⟩ := (meromorphicOrderAt_eq_int_iff hF).1 hn
  refine ⟨fun z => (n : ℂ) * dslope E a z + E z * (deriv G z / G z),
    (analyticAt_const.mul (analyticAt_dslope hE)).add (hE.mul (hGan.deriv.div hGan hG0)), ?_⟩
  have ha : ∀ᶠ z in 𝓝[≠] a, AnalyticAt ℂ G z :=
    eventually_nhdsWithin_of_eventually_nhds hGan.eventually_analyticAt
  have hb : ∀ᶠ z in 𝓝[≠] a, G z ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds (hGan.continuousAt.eventually_ne hG0)
  have hd : ∀ᶠ z in 𝓝[≠] a, z ≠ a := eventually_mem_nhdsWithin
  filter_upwards [eventually_nhdsNE_eventually_nhds hev, ha, hb, hd, hev] with z hz hGz hGz0 hza hfz
  have hderiv : deriv F z = deriv (fun w => (w - a) ^ n * G w) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hz] with u hu
    rw [hu, smul_eq_mul]
  rw [hderiv, hfz, smul_eq_mul, deriv_zpow_mul_div n hza hGz.differentiableAt hGz0,
    dslope_of_ne _ hza, slope_def_field]
  have hsub : z - a ≠ 0 := sub_ne_zero.2 hza
  field_simp
  ring

theorem main (U : Set ℂ) (hU : IsOpen U) (F : ℂ → ℂ) (hF : ∀ z ∈ U, MeromorphicAt F z)
    (hF' : ∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤)
    (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E U)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, E z * (deriv F z / F z) * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) =
      -π * ∑ᶠ a, (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a * h a := by
  have hEan : AnalyticOnNhd ℂ E U := hE.analyticOnNhd hU
  set c : ℂ → ℂ := fun a => (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a with hc
  have hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, E z * (deriv F z / F z) = c a / (z - a) + g z := by
    intro a ha
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hF' a ha)
    obtain ⟨g, hg, hev⟩ := hloc_logDeriv (hF a ha) hn.symm (hEan a ha)
    refine ⟨g, hg, ?_⟩
    have hca : c a = (n : ℂ) * E a := by simp [hc, ← hn]
    rw [hca]
    exact hev
  have := Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue U hU
    (fun z => E z * (deriv F z / F z)) c hloc h hh hsupp hU'
  simpa only [hc, mul_assoc] using this

end Complex.LogDerivStokes

theorem solution
    (U : Set ℂ) (hU : IsOpen U) (F : ℂ → ℂ) (hF : ∀ z ∈ U, MeromorphicAt F z)
    (hF' : ∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤)
    (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E U)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, E z * (deriv F z / F z) * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) =
      -π * ∑ᶠ a, (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a * h a :=
  Complex.LogDerivStokes.main U hU F hF hF' E hE h hh hsupp hU'

end

end S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum
end P2MW
export P2MW.S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum (solution)
