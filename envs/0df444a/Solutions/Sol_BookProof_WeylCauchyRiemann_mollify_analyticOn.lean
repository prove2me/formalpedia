-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.mollify_analyticOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:43.13225+00:00
-- url     : https://prove2.me/submissions/23fa081b-6acb-4811-9efe-94f87bbb728a

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.mollify_analyticOn
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_analyticOn_of_dbar_eq_zero
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_contDiff
import Theorems.Thm_BookProof_WeylCauchyRiemann_dbar_ofReal_comp_sub
import Theorems.Thm_BookProof_WeylCauchyRiemann_dbar_mollify
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {f : ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyIntegrableOn f U) (hCR : WeakCauchyRiemannOn f U)
    {c : ℂ} {R r δ : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hrR : r + δ ≤ R)
    (hKU : closedBall c R ⊆ U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hsupp : Function.support χ ⊆ ball (0 : ℂ) δ) :
    AnalyticOn ℂ (mollify ((closedBall c R).indicator f) χ) (ball c r) := by

  set F : ℂ → ℂ := (closedBall c R).indicator f with hFdef
  have hRpos : 0 < R := by linarith
  have hFint : Integrable F := by
    rw [hFdef]
    exact (integrable_indicator_iff measurableSet_closedBall).2
      (hf.integrableOn_compact_subset hKU (isCompact_closedBall c R))
  have hFloc : LocallyIntegrable F := hFint.locallyIntegrable
  have hsmooth : ContDiff ℝ ∞ (mollify F χ) := mollify_contDiff hFloc hχ hχc
  have htsupp : tsupport χ ⊆ closedBall (0 : ℂ) δ :=
    closure_minimal (hsupp.trans ball_subset_closedBall) isClosed_closedBall
  refine analyticOn_of_dbar_eq_zero isOpen_ball
    (fun z _ => (hsmooth.differentiable (by simp)) z) ?_
  intro z hz
  have hzc : ‖z - c‖ < r := by
    simpa [Complex.dist_eq] using mem_ball.1 hz
  -- the reflected kernel is a legitimate test function
  set φ : ℂ → ℂ := fun v => ((χ (z - v) : ℝ) : ℂ) with hφdef
  have hφsmooth : ContDiff ℝ ∞ φ :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp (contDiff_const.sub contDiff_id))
  have hφsupp : Function.support φ ⊆ closedBall z δ := by
    intro v hv
    simp only [hφdef, Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hv
    have : z - v ∈ ball (0 : ℂ) δ := hsupp hv
    simp only [mem_ball, dist_zero_right] at this
    simp only [mem_closedBall, Complex.dist_eq]
    rw [← norm_neg]
    simpa using this.le
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z δ) hφsupp
  have hφU : tsupport φ ⊆ U := by
    refine subset_trans (closure_minimal hφsupp isClosed_closedBall) (subset_trans ?_ hKU)
    intro v hv
    simp only [mem_closedBall, Complex.dist_eq] at hv ⊢
    calc ‖v - c‖ = ‖(v - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖v - z‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ δ + ‖z - c‖ := by
          have : ‖v - z‖ = ‖z - v‖ := by rw [← norm_neg]; ring_nf
          rw [this]; linarith [hv]
      _ ≤ R := by linarith
  have hweak := hCR φ hφsmooth hφc hφU
  -- rewrite the weak equation as the vanishing of the mollified `∂̄`
  have hdb : ∀ w : ℂ, dbar φ w = -dbarR χ (z - w) := fun w =>
    dbar_ofReal_comp_sub hχ z w
  have hzero : ∫ w : ℂ, dbarR χ (z - w) * f w = 0 := by
    have : ∫ w : ℂ, f w * dbar φ w = -∫ w : ℂ, dbarR χ (z - w) * f w := by
      rw [← MeasureTheory.integral_neg]
      congr 1
      funext w
      rw [hdb w]
      ring
    rw [this] at hweak
    exact neg_eq_zero.1 hweak
  have hFf : ∀ w : ℂ, dbarR χ (z - w) * F w = dbarR χ (z - w) * f w := by
    intro w
    by_cases hd : dbarR χ (z - w) = 0
    · simp [hd]
    · have hsupp' : z - w ∈ tsupport χ := by
        by_contra hcon
        have hz0 : fderiv ℝ χ (z - w) = 0 := by
          have := support_fderiv_subset (𝕜 := ℝ) (f := χ)
          by_contra hne
          exact hcon (this (by simpa [Function.mem_support] using hne))
        apply hd
        simp [dbarR, hz0]
      have hwmem : w ∈ closedBall c R := by
        have h1 : ‖z - w‖ ≤ δ := by
          have := htsupp hsupp'
          simpa [mem_closedBall, dist_zero_right] using this
        simp only [mem_closedBall, Complex.dist_eq]
        calc ‖w - c‖ = ‖-(z - w) + (z - c)‖ := by ring_nf
          _ ≤ ‖-(z - w)‖ + ‖z - c‖ := norm_add_le _ _
          _ ≤ δ + ‖z - c‖ := by rw [norm_neg]; linarith
          _ ≤ R := by linarith
      rw [hFdef, Set.indicator_of_mem hwmem]
  rw [dbar_mollify hFloc hχ hχc z]
  calc ∫ w : ℂ, dbarR χ (z - w) * F w
      = ∫ w : ℂ, dbarR χ (z - w) * f w := by
        congr 1
        funext w
        exact hFf w
    _ = 0 := hzero
