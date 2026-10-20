-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.exists_analyticOn_ae_eq_ball
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:49.840748+00:00
-- url     : https://prove2.me/submissions/ca547cb5-5701-4c27-ab92-6b0aead60930

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.exists_analyticOn_ae_eq_ball
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_contDiff
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_analyticOn
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_comm
import Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_moll_eq_self
import Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_rOut_tendsto
import Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_support
import Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_contDiff
import Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_hasCompactSupport
import Theorems.Thm_BookProof_WeylCauchyRiemann_ae_tendsto_mollify_bump
import Theorems.Thm_BookProof_WeylCauchyRiemann_tendsto_mollify_bump_of_continuous
import Theorems.Thm_BookProof_RadialMollifier_moll_contDiff
import Theorems.Thm_BookProof_RadialMollifier_moll_continuous
import Theorems.Thm_BookProof_RadialMollifier_moll_hasCompactSupport
import Theorems.Thm_BookProof_RadialMollifier_moll_support_subset
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {f : ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyIntegrableOn f U) (hCR : WeakCauchyRiemannOn f U)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hKU : closedBall c R ⊆ U) :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g (ball c (R / 4)) ∧
      ∀ᵐ z : ℂ, z ∈ ball c (R / 4) → f z = g z := by

  set δ : ℝ := R / 4 with hδdef
  have hδ : 0 < δ := by positivity
  set F : ℂ → ℂ := (closedBall c R).indicator f with hFdef
  have hFint : Integrable F := by
    rw [hFdef]
    exact (integrable_indicator_iff measurableSet_closedBall).2
      (hf.integrableOn_compact_subset hKU (isCompact_closedBall c R))
  have hFloc : LocallyIntegrable F := hFint.locallyIntegrable
  set h : ℂ → ℂ := mollify F (moll δ) with hhdef
  have hsmooth : ContDiff ℝ ∞ h :=
    mollify_contDiff hFloc (moll_contDiff δ) (moll_hasCompactSupport hδ)
  have hcont : Continuous h := hsmooth.continuous
  have hana : AnalyticOn ℂ h (ball c (R / 2)) :=
    mollify_analyticOn hf hCR hδ (by positivity) (by linarith) hKU
      (moll_contDiff δ) (moll_hasCompactSupport hδ) (moll_support_subset hδ)
  refine ⟨h, hana.mono (ball_subset_ball (by linarith)), ?_⟩
  -- the bump mollifications are holomorphic too, for small radii
  have hev : ∀ᶠ n in atTop, (bumpSeq n).rOut < δ :=
    Filter.Tendsto.eventually_lt_const hδ bumpSeq_rOut_tendsto
  have hbana : ∀ n, (bumpSeq n).rOut < δ →
      AnalyticOn ℂ (mollify F ((bumpSeq n).normed volume)) (ball c (R / 2)) := by
    intro n hn
    refine mollify_analyticOn hf hCR hδ (by positivity) (by linarith) hKU
      (bumpSeq_contDiff n) (bumpSeq_hasCompactSupport n) ?_
    exact (bumpSeq_support n).trans (ball_subset_ball hn.le)
  -- for small radii the two mollifications agree on the small ball
  have hkey : ∀ n, (bumpSeq n).rOut < δ → ∀ z ∈ ball c (R / 4),
      mollify F ((bumpSeq n).normed volume) z = mollify h ((bumpSeq n).normed volume) z := by
    intro n hn z hz
    have hball : closedBall z δ ⊆ ball c (R / 2) := by
      intro v hv
      have h1 : dist v z ≤ δ := mem_closedBall.1 hv
      have h2 : dist z c < R / 4 := mem_ball.1 hz
      have : dist v c < R / 2 := by
        calc dist v c ≤ dist v z + dist z c := dist_triangle _ _ _
          _ < δ + R / 4 := by linarith
          _ = R / 2 := by rw [hδdef]; ring
      exact mem_ball.2 this
    have hbcont : Continuous (mollify F ((bumpSeq n).normed volume)) :=
      (mollify_contDiff hFloc (bumpSeq_contDiff n) (bumpSeq_hasCompactSupport n)).continuous
    have h1 : mollify (mollify F ((bumpSeq n).normed volume)) (moll δ) z
        = mollify F ((bumpSeq n).normed volume) z :=
      mollify_moll_eq_self isOpen_ball ((hbana n hn).differentiableOn) hbcont hδ hball
    have h2 : mollify (mollify F ((bumpSeq n).normed volume)) (moll δ)
        = mollify (mollify F (moll δ)) ((bumpSeq n).normed volume) :=
      mollify_comm hFint (bumpSeq_contDiff n).continuous (bumpSeq_hasCompactSupport n)
        (moll_continuous δ) (moll_hasCompactSupport hδ)
    rw [← h1, h2, hhdef]
  -- pass to the limit
  filter_upwards [ae_tendsto_mollify_bump hFloc] with z hzlim hzmem
  have hlim2 : Tendsto (fun n => mollify h ((bumpSeq n).normed volume) z) atTop (nhds (h z)) :=
    tendsto_mollify_bump_of_continuous hcont z
  have hlim1 : Tendsto (fun n => mollify F ((bumpSeq n).normed volume) z) atTop (nhds (h z)) := by
    refine hlim2.congr' ?_
    filter_upwards [hev] with n hn
    exact (hkey n hn z hzmem).symm
  have hFz : F z = h z := tendsto_nhds_unique hzlim hlim1
  have hzin : z ∈ closedBall c R := by
    have : dist z c < R / 4 := mem_ball.1 hzmem
    exact mem_closedBall.2 (by linarith)
  rwa [hFdef, Set.indicator_of_mem hzin] at hFz
