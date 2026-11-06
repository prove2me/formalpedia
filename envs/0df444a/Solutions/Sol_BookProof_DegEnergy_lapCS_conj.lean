-- Prove2me | solution 1 for BookProof.DegEnergy.lapCS_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T16:12:35.045394+00:00
-- url     : https://prove2.me/submissions/6e5984c3-2edc-4ffa-bf36-03e308655e77

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.lapCS_conj
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
import Theorems.Thm_BookProof_DegEnergy_dcoord_conj
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterHermiteProductCore
open BookProof.DegEnergy




open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.ConvolutionCalc
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (S : Finset (Fin d)) (y : Vd d) :
    (starRingEnd ℂ) (lapCS S g y) = lapCS S (fun t => (starRingEnd ℂ) (g t)) y := by

  have hstep : ∀ j : Fin d, (starRingEnd ℂ) (dcoord j (dcoord j g) y)
      = dcoord j (dcoord j (fun t => (starRingEnd ℂ) (g t))) y := by
    intro j
    have h1 : (fun t => (starRingEnd ℂ) (dcoord j g t)) = dcoord j (fun t =>
        (starRingEnd ℂ) (g t)) := by
      funext t
      exact (dcoord_conj hg j t).symm
    rw [← dcoord_conj (contDiff_dcoord hg j) j y, h1]
  simp only [lapCS, map_sum, hstep]
