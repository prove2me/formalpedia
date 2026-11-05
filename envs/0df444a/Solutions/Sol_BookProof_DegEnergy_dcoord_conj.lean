-- Prove2me | solution 1 for BookProof.DegEnergy.dcoord_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:39:04.2982+00:00
-- url     : https://prove2.me/submissions/9bda21df-8a50-4555-b0a4-36af9a009cff

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.dcoord_conj
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
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
theorem solution {v : Vd d → ℂ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (j : Fin d)
    (x : Vd d) :
    dcoord j (fun y => (starRingEnd ℂ) (v y)) x = (starRingEnd ℂ) (dcoord j v x) := by

  have hd : HasFDerivAt v (fderiv ℝ v x) x :=
    (hv.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hc : HasFDerivAt (fun y => (starRingEnd ℂ) (v y))
      ((Complex.conjLIE.toLinearIsometry.toContinuousLinearMap).comp (fderiv ℝ v x)) x :=
    (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.hasFDerivAt).comp x hd
  simp only [dcoord]
  rw [hc.fderiv]
  rfl
