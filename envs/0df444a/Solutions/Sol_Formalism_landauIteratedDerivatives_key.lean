-- Prove2me | solution 1 for Formalism.landauIteratedDerivatives.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:44.955598+00:00
-- url     : https://prove2.me/submissions/e1b60f25-bd99-4301-9c94-9a4b1623fe20

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
import Theorems.Thm_Formalism_landauIteratedDerivatives_good_logpow
import Theorems.Thm_Formalism_landauIteratedDerivatives_hasDerivAt_J
import Theorems.Thm_Formalism_landauIteratedDerivatives_iteratedDeriv_J
import Theorems.Thm_Formalism_landauIteratedDerivatives_term_eq
import Theorems.Thm_Formalism_landauIteratedDerivatives_integrable_of_series
import Theorems.Thm_P2M_Formalism_landauIteratedDerivatives_dist_ofReal__31aeae0510ba
import Theorems.Thm_Formalism_landauIteratedDerivatives_dist_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open Formalism.landauIteratedDerivatives
namespace Formalism.landauIteratedDerivatives
theorem _root_.solution (hMD : MellinDeriv) {H : ℝ → ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    {b σc : ℝ} (hσcb : σc ≤ b) (hgood : ∀ σ, σc < σ → Good H σ) {Φ : ℂ → ℂ}
    (hΦ1 : ∀ s : ℂ, b < s.re → AnalyticAt ℂ Φ s)
    (hΦ2 : ∀ σ : ℝ, σc ≤ σ → σ ≤ b → AnalyticAt ℂ Φ σ)
    (hΦeq : ∀ s : ℂ, b < s.re → Φ s = J H 0 s) : ∃ σ' < σc, Good H σ' := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_Icc.image continuous_ofReal : IsCompact ((fun σ : ℝ => (σ : ℂ)) '' Icc σc b)).exists_thickening_subset_open
      (isOpen_analyticAt ℂ Φ) (by rintro _ ⟨σ, ⟨h1, h2⟩, rfl⟩; exact hΦ2 σ h1 h2)
  have hA : ∀ z : ℂ, (b < z.re ∨ ∃ σ : ℝ, σc ≤ σ ∧ σ ≤ b ∧ dist z σ < δ) → AnalyticAt ℂ Φ z := by
    rintro z (h | ⟨σ, h1, h2, h3⟩)
    · exact hΦ1 z h
    · exact hthick (Metric.mem_thickening_iff.2 ⟨σ, ⟨σ, ⟨h1, h2⟩, rfl⟩, h3⟩)
  set R : Set ℂ := {z : ℂ | σc < z.re} ∩ {z : ℂ | z.im < δ} ∩ {z : ℂ | -δ < z.im} with hR
  have hRopen : IsOpen R :=
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_im continuous_const)).inter
      (isOpen_lt continuous_const continuous_im)
  have hRconv : Convex ℝ R :=
    ((convex_halfSpace_re_gt σc).inter (convex_halfSpace_im_lt δ)).inter (convex_halfSpace_im_gt (-δ))
  have hΦR : AnalyticOnNhd ℂ Φ R := by
    rintro z ⟨⟨h1, h2⟩, h3⟩
    apply hA
    by_cases hb : b < z.re
    · exact Or.inl hb
    · refine Or.inr ⟨z.re, le_of_lt h1, not_lt.1 hb, ?_⟩
      rw [dist_re]
      exact abs_lt.2 ⟨h3, h2⟩
  have hJan : AnalyticOnNhd ℂ (J H 0) {z : ℂ | σc < z.re} :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (hasDerivAt_J hMD hH hpos hgood 0 hz).differentiableAt.differentiableWithinAt)
      (isOpen_lt continuous_const continuous_re)
  have hEq : EqOn Φ (J H 0) R := by
    have hz0 : ((b + 1 : ℝ) : ℂ) ∈ R := by
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp <;> linarith
    refine hΦR.eqOn_of_preconnected_of_eventuallyEq (hJan.mono (fun z hz => hz.1.1))
      hRconv.isPreconnected hz0 ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show b < (((b + 1 : ℝ) : ℂ)).re by simp)] with w hw
    exact hΦeq w hw
  set cr : ℝ := σc + δ / 4 with hcr
  have hcR : (cr : ℂ) ∈ R := by
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [hcr] <;> linarith
  have hev : Φ =ᶠ[𝓝 (cr : ℂ)] J H 0 := by
    filter_upwards [hRopen.mem_nhds hcR] with w hw
    exact hEq hw
  have hder : ∀ n : ℕ, iteratedDeriv n Φ (cr : ℂ) = J H n (cr : ℂ) := fun n =>
    (hev.iteratedDeriv_eq n).trans
      (iteratedDeriv_J hMD hH hpos hgood n (cr : ℂ) (by simp [hcr]; linarith))
  have hdiff : DifferentiableOn ℂ Φ (Metric.ball (cr : ℂ) (δ / 2)) := by
    intro z hz
    refine (hA z ?_).differentiableAt.differentiableWithinAt
    rw [Metric.mem_ball] at hz
    by_cases hb : b < z.re
    · exact Or.inl hb
    · right
      have him : |z.im| < δ / 2 := by
        have := Complex.abs_im_le_norm (z - cr)
        rw [← dist_eq_norm] at this
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
        linarith
      by_cases hs : σc ≤ z.re
      · refine ⟨z.re, hs, not_lt.1 hb, ?_⟩
        rw [dist_re]; linarith
      · refine ⟨σc, le_rfl, hσcb, ?_⟩
        have h1 : dist (cr : ℂ) (σc : ℂ) = δ / 4 := by
          rw [dist_ofReal', hcr, show σc + δ / 4 - σc = δ / 4 by ring,
            abs_of_pos (by linarith)]
        linarith [dist_triangle z (cr : ℂ) (σc : ℂ)]
  set t : ℝ := 3 * δ / 8 with ht
  have hzmem : ((cr - t : ℝ) : ℂ) ∈ Metric.ball (cr : ℂ) (δ / 2) := by
    rw [Metric.mem_ball, dist_ofReal', show cr - t - cr = -t by ring, abs_neg,
      abs_of_pos (by rw [ht]; linarith)]
    rw [ht]; linarith
  have hs := Complex.hasSum_taylorSeries_on_ball hdiff hzmem
  have hsub : ((cr - t : ℝ) : ℂ) - (cr : ℂ) = -(t : ℂ) := by push_cast; ring
  simp_rw [hsub, hder, term_eq] at hs
  have hsum := Complex.summable_ofReal.1 hs.summable
  have hint : ∀ n : ℕ, IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-cr - 1))) (Ioi 1) :=
    fun n => good_logpow hH (hgood (σc + δ / 8) (by linarith)) (by rw [hcr]; linarith) n
  refine ⟨cr - t, by rw [hcr, ht]; linarith, ?_⟩
  exact integrable_of_series hH hpos (by rw [ht]; positivity) hint hsum
end Formalism.landauIteratedDerivatives
