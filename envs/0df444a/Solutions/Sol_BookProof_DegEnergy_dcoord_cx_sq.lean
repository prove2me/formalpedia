-- Prove2me | solution 1 for BookProof.DegEnergy.dcoord_cx_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T16:12:43.510917+00:00
-- url     : https://prove2.me/submissions/3351659f-8a7b-43a5-829d-4ce25e9e2b3a

-- Generated from ChapterDegEnergyEstimate.lean — solution of BookProof.DegEnergy.dcoord_cx_sq
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
import Theorems.Thm_BookProof_DegEnergy_contDiff_cx
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
variable (S : Finset (Fin d))

set_option maxHeartbeats 1000000 in
theorem solution {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (j : Fin d)
    (x : Vd d) : dcoord j (fun y => cx χ y ^ 2) x = 2 * cx χ x * dcoord j (cx χ) x := by

  have h : (fun y => cx χ y ^ 2) = fun y => cx χ y * cx χ y := by funext y; ring
  rw [h, dcoord_mul (contDiff_cx hχ) (contDiff_cx hχ)]
  ring
