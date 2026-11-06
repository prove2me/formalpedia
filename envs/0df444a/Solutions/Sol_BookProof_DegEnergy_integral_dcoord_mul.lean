-- Prove2me | solution 1 for BookProof.DegEnergy.integral_dcoord_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T16:12:39.249196+00:00
-- url     : https://prove2.me/submissions/88572da9-5a08-484d-b6c7-32a46ad477ef

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.integral_dcoord_mul
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
import Theorems.Thm_BookProof_DegEnergy_integrable_of_cc
import Theorems.Thm_BookProof_ConvolutionCalc_hasCompactSupport_dcoord
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
theorem solution {f g : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (j : Fin d) :
    ∫ x, f x * dcoord j g x = -∫ x, dcoord j f x * g x := by

  have hfcont : Continuous f := hf.continuous
  have hgcont : Continuous g := hg.continuous
  have hdf : Continuous (dcoord j f) := (contDiff_dcoord hf j).continuous
  have hdg : Continuous (dcoord j g) := (contDiff_dcoord hg j).continuous
  have hdfc : HasCompactSupport (dcoord j f) := hasCompactSupport_dcoord hfc j
  have h1 : Integrable (fun x => dcoord j f x * g x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hdf.mul hgcont) (hdfc.mul_right)
  have h2 : Integrable (fun x => f x * dcoord j g x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hfcont.mul hdg) (hfc.mul_right)
  have h3 : Integrable (fun x => f x * g x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hfcont.mul hgcont) (hfc.mul_right)
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hfd.differentiableAt) (fun x _ => hgd.differentiableAt)
