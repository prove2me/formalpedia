-- Prove2me | solution 1 for BookProof.ConvolutionCalc.lapCS_reflect
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T17:44:49.315663+00:00
-- url     : https://prove2.me/submissions/dda19c45-2487-4351-b6f9-fd7e32890539

-- Generated from ChapterConvolutionCalc.lean — solution of BookProof.ConvolutionCalc.lapCS_reflect
import Mathlib
import Definitions.Def_ChapterConvolutionCalc
import Theorems.Thm_BookProof_ConvolutionCalc_dcoord_reflect
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ConvolutionCalc




open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : Vd d)
    (S : Finset (Fin d)) (y : Vd d) :
    lapCS S (fun y => g (x - y)) y = lapCS S g (x - y) := by

  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : dcoord j (fun y => g (x - y)) = fun y => (-(dcoord j g)) (x - y) := by
    rw [dcoord_reflect hg x j]
    funext w
    simp
  have h2 : dcoord j (fun y => (-(dcoord j g)) (x - y))
      = fun y => -(dcoord j (-(dcoord j g)) (x - y)) :=
    dcoord_reflect ((contDiff_dcoord hg j).neg) x j
  rw [h1, h2]
  have h3 : dcoord j (-(dcoord j g)) = -(dcoord j (dcoord j g)) := by
    funext w
    simp only [dcoord, Pi.neg_apply]
    rw [fderiv_neg]
    simp
  rw [h3]
  simp
