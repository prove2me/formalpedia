-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.weak_cauchyRiemann_iff_ae_eq_analytic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:39:57.841517+00:00
-- url     : https://prove2.me/submissions/099ec372-7f0d-4cb1-85be-b931eaf04783

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.weak_cauchyRiemann_iff_ae_eq_analytic
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_weak_cauchyRiemann_ae_eq_analytic
import Theorems.Thm_BookProof_WeylCauchyRiemann_weakCauchyRiemannOn_of_analyticOn
import Theorems.Thm_BookProof_WeylCauchyRiemann_WeakCauchyRiemannOn_congr_ae
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U) :
    WeakCauchyRiemannOn f U ↔ ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ ∀ᵐ z : ℂ, z ∈ U → f z = g z := by

  refine ⟨fun hCR => weak_cauchyRiemann_ae_eq_analytic hU hf hCR, ?_⟩
  rintro ⟨g, hg, hae⟩
  exact (weakCauchyRiemannOn_of_analyticOn hU hg).congr_ae hae
