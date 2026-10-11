-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.weakCauchyRiemannOn_of_analyticOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:39:41.975107+00:00
-- url     : https://prove2.me/submissions/f03f0950-b9be-43f1-8ff5-24f894ce1dbd

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.weakCauchyRiemannOn_of_analyticOn
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_integral_dbar_eq_zero
import Theorems.Thm_BookProof_WeylCauchyRiemann_dbar_eq_zero_of_differentiableAt
import Theorems.Thm_BookProof_WeylCauchyRiemann_dbar_mul
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOn ℂ g U) : WeakCauchyRiemannOn g U := by

  classical
  intro φ hφ hφc hφU
  have hgn : AnalyticOnNhd ℂ g U := (hU.analyticOn_iff_analyticOnNhd.1 hg)
  set ψ : ℂ → ℂ := fun z => if z ∈ U then g z * φ z else 0 with hψdef
  have hUmem : ∀ z ∈ U, ψ =ᶠ[𝓝 z] fun w => g w * φ w := by
    intro z hz
    filter_upwards [hU.mem_nhds hz] with w hw
    simp [hψdef, hw]
  have hφ0 : ∀ z ∉ tsupport φ, φ =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    filter_upwards [(isOpen_compl_iff.2 (isClosed_tsupport φ)).mem_nhds hz] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  have hout : ∀ z ∉ tsupport φ, ψ =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    filter_upwards [(isOpen_compl_iff.2 (isClosed_tsupport φ)).mem_nhds hz] with w hw
    have : φ w = 0 := image_eq_zero_of_notMem_tsupport hw
    simp [hψdef, this]
  have hψsmooth : ContDiff ℝ ∞ ψ := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · have h1 : ContDiffAt ℝ ∞ (fun w => g w * φ w) z :=
        (((hgn z hz).contDiffAt).restrict_scalars ℝ).mul hφ.contDiffAt
      exact h1.congr_of_eventuallyEq (hUmem z hz)
    · have hz' : z ∉ tsupport φ := fun h => hz (hφU h)
      exact contDiffAt_const.congr_of_eventuallyEq (hout z hz')
  have hψc : HasCompactSupport ψ := by
    refine HasCompactSupport.of_support_subset_isCompact hφc.isCompact ?_
    intro z hz
    by_contra h
    exact hz ((hout z h).self_of_nhds)
  have key : ∀ z, g z * dbar φ z = dbar ψ z := by
    intro z
    by_cases hz : z ∈ U
    · have h1 : dbar ψ z = dbar (fun w => g w * φ w) z := by
        simp only [dbar, (hUmem z hz).fderiv_eq]
      have hga : DifferentiableAt ℂ g z := (hgn z hz).differentiableAt
      rw [h1, dbar_mul (hga.restrictScalars ℝ) (hφ.differentiable (by simp) z),
        dbar_eq_zero_of_differentiableAt hga]
      ring
    · have hz' : z ∉ tsupport φ := fun h => hz (hφU h)
      have h1 : dbar ψ z = 0 := by
        simp only [dbar, (hout z hz').fderiv_eq]
        simp
      have h2 : dbar φ z = 0 := by
        simp only [dbar, (hφ0 z hz').fderiv_eq]
        simp
      rw [h1, h2, mul_zero]
  calc ∫ z : ℂ, g z * dbar φ z = ∫ z : ℂ, dbar ψ z := by simp only [key]
    _ = 0 := integral_dbar_eq_zero hψsmooth hψc
