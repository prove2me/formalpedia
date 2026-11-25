-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.hol_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:32:18.92706+00:00
-- url     : https://prove2.me/submissions/0edb6e7e-d213-4730-ae5c-66a65dd2a6c9

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_isOpen_annT
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_circleMap_mem_annT
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_im_conj_dZ_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_winding
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_continuousOn_dZ

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
    ∃ n : ℤ, (circleIntegral (fun w => star (u w) * NF.dZ u w) 0 R).im = Real.pi * n := by
  have hopen := isOpen_annT TT
  have hmem : ∀ θ, circleMap 0 R θ ∈ AnnT TT := circleMap_mem_annT hR
  obtain ⟨n, hn⟩ := winding hu h1 hR
  refine ⟨n, ?_⟩
  have hf := hu.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hc : Continuous (circleMap 0 R) := continuous_circleMap 0 R
  have h2 : Continuous fun θ => fderiv ℝ u (circleMap 0 R θ) := hf.comp_continuous hc hmem
  have h3 : Continuous fun θ => u (circleMap 0 R θ) := hu.continuousOn.comp_continuous hc hmem
  have hdz : Continuous fun θ => NF.dZ u (circleMap 0 R θ) := (continuousOn_dZ hu).comp_continuous hc hmem
  set f1 : ℝ → ℂ := fun θ => deriv (circleMap 0 R) θ •
    (star (u (circleMap 0 R θ)) * NF.dZ u (circleMap 0 R θ)) with hf1def
  set f2 : ℝ → ℂ := fun θ => star (u (circleMap 0 R θ)) *
    fderiv ℝ u (circleMap 0 R θ) (circleMap 0 R θ * Complex.I) with hf2def
  have hf1 : Continuous f1 := by
    rw [hf1def]
    simp only [deriv_circleMap, smul_eq_mul]
    exact (hc.mul continuous_const).mul ((continuous_star.comp h3).mul hdz)
  have hf2 : Continuous f2 := (continuous_star.comp h3).mul (h2.clm_apply (hc.mul continuous_const))
  have hpt : ∀ θ, (f1 θ).im = (f2 θ).im / 2 := by
    intro θ
    rw [hf1def, hf2def]
    simp only [deriv_circleMap, smul_eq_mul]
    rw [show circleMap 0 R θ * Complex.I * (star (u (circleMap 0 R θ)) * NF.dZ u (circleMap 0 R θ)) =
      star (u (circleMap 0 R θ)) * NF.dZ u (circleMap 0 R θ) * (circleMap 0 R θ * Complex.I) by ring]
    exact im_conj_dZ_mul hu h1 (hmem θ) _
  have hI1 : (circleIntegral (fun w => star (u w) * NF.dZ u w) 0 R).im =
      ∫ θ in (0 : ℝ)..2 * Real.pi, (f1 θ).im := by
    rw [circleIntegral]
    exact (intervalIntegral.intervalIntegral_im (hf1.intervalIntegrable _ _)).symm
  have hI2 : ∫ θ in (0 : ℝ)..2 * Real.pi, (f2 θ).im = (∫ θ in (0 : ℝ)..2 * Real.pi, f2 θ).im :=
    intervalIntegral.intervalIntegral_im (hf2.intervalIntegrable _ _)
  rw [hI1]
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, hI2]
  have hn' : (∫ θ in (0 : ℝ)..2 * Real.pi, f2 θ).im = 2 * Real.pi * n := hn
  rw [hn']
  ring
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
