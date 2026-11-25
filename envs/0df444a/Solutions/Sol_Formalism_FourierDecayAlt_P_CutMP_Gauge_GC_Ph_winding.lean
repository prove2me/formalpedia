-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.winding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:56.216733+00:00
-- url     : https://prove2.me/submissions/001cd17b-6c64-4f59-a092-d4ada574575d

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_isOpen_annT
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_circleMap_mem_annT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
theorem _root_.solution {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT))
    (h1 : ∀ ζ ∈ AnnT TT, ‖u ζ‖ = 1) {R : ℝ} (hR : TT < R ^ 2) :
    ∃ n : ℤ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      star (u (circleMap 0 R θ)) * fderiv ℝ u (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)).im =
        2 * Real.pi * n := by
  have hopen := isOpen_annT TT
  have hmem : ∀ θ, circleMap 0 R θ ∈ AnnT TT := circleMap_mem_annT hR
  have hdiff : ∀ ζ ∈ AnnT TT, DifferentiableAt ℝ u ζ := fun ζ hζ =>
    (hu.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hζ)
  have hv : ∀ θ, HasDerivAt (fun t => u (circleMap 0 R t))
      (fderiv ℝ u (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) θ := by
    intro θ
    exact (hdiff _ (hmem θ)).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 R θ)
  set g : ℝ → ℂ := fun θ => star (u (circleMap 0 R θ)) *
    fderiv ℝ u (circleMap 0 R θ) (circleMap 0 R θ * Complex.I) with hgdef
  have hgcont : Continuous g := by
    have hf := hu.continuousOn_fderiv_of_isOpen hopen (by simp)
    have hc : Continuous (circleMap 0 R) := continuous_circleMap 0 R
    have h2 : Continuous fun θ => fderiv ℝ u (circleMap 0 R θ) := hf.comp_continuous hc hmem
    have h3 : Continuous fun θ => u (circleMap 0 R θ) := hu.continuousOn.comp_continuous hc hmem
    exact (continuous_star.comp h3).mul (h2.clm_apply (hc.mul continuous_const))
  set G : ℝ → ℂ := fun t => ∫ θ in (0 : ℝ)..t, g θ with hGdef
  have hG : ∀ t, HasDerivAt G (g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hgcont.intervalIntegrable _ _)
      (hgcont.stronglyMeasurableAtFilter _ _) hgcont.continuousAt
  have hnorm : ∀ t, u (circleMap 0 R t) * star (u (circleMap 0 R t)) = 1 := by
    intro t
    have hn := h1 _ (hmem t)
    have e : u (circleMap 0 R t) * star (u (circleMap 0 R t)) = (Complex.normSq (u (circleMap 0 R t)) : ℂ) :=
      Complex.mul_conj _
    rw [e, Complex.normSq_eq_norm_sq, hn]
    simp
  have hF : ∀ t, HasDerivAt (fun t => u (circleMap 0 R t) * Complex.exp (-G t)) 0 t := by
    intro t
    have h4 := (hv t).mul ((hG t).neg.cexp)
    have h0 : fderiv ℝ u (circleMap 0 R t) (circleMap 0 R t * Complex.I) * Complex.exp (-G t) +
        u (circleMap 0 R t) * (Complex.exp (-G t) * -g t) = 0 := by
      rw [hgdef]
      beta_reduce
      linear_combination -(Complex.exp (-G t) * fderiv ℝ u (circleMap 0 R t) (circleMap 0 R t * Complex.I)) * hnorm t
    exact h4.congr_deriv h0
  have hconst := is_const_of_deriv_eq_zero (fun t => (hF t).differentiableAt) (fun t => (hF t).deriv)
    (2 * Real.pi) 0
  have hv2 : circleMap 0 R (2 * Real.pi) = circleMap 0 R 0 := by
    simpa using periodic_circleMap 0 R 0
  have hv0 : u (circleMap 0 R 0) ≠ 0 := by
    intro h0
    have hn := h1 _ (hmem 0)
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have hE : Complex.exp (-G (2 * Real.pi)) = 1 := by
    have h5 : u (circleMap 0 R 0) * Complex.exp (-G (2 * Real.pi)) = u (circleMap 0 R 0) * 1 := by
      have h6 := hconst
      simp only [hG0, neg_zero, Complex.exp_zero, mul_one] at h6
      rw [hv2] at h6
      rw [mul_one]
      exact h6
    exact mul_left_cancel₀ hv0 h5
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hE
  refine ⟨-n, ?_⟩
  have h7 : G (2 * Real.pi) = -(n * (2 * Real.pi * Complex.I)) := by
    rw [← hn]
    ring
  show (G (2 * Real.pi)).im = 2 * Real.pi * ((-n : ℤ) : ℝ)
  rw [h7]
  simp
  ring
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
