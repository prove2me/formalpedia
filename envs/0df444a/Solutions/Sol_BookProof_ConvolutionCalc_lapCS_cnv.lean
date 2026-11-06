-- Prove2me | solution 1 for BookProof.ConvolutionCalc.lapCS_cnv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T17:54:47.956902+00:00
-- url     : https://prove2.me/submissions/e4c75312-f896-4dab-ada0-8e5ff010e354

-- Generated from ChapterConvolutionCalc.lean — solution of BookProof.ConvolutionCalc.lapCS_cnv
import Mathlib
import Definitions.Def_ChapterConvolutionCalc
import Theorems.Thm_BookProof_ConvolutionCalc_hasCompactSupport_dcoord
import Theorems.Thm_BookProof_ConvolutionCalc_dcoord_cnv
import Theorems.Thm_BookProof_ConvolutionCalc_cnv_finset_sum
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
theorem solution {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (S : Finset (Fin d)) (x : Vd d) :
    lapCS S (cnv u ρ) x = cnv u (lapCS S ρ) x := by

  have hd : ∀ j : Fin d, dcoord j (dcoord j (cnv u ρ)) = cnv u (dcoord j (dcoord j ρ)) := by
    intro j
    rw [dcoord_cnv hu hρ hc j,
      dcoord_cnv hu (contDiff_dcoord hρ j) (hasCompactSupport_dcoord hc j) j]
  have hsum := cnv_finset_sum (u := u) (g := fun j => dcoord j (dcoord j ρ)) S hu
    (fun j _ => (contDiff_dcoord (contDiff_dcoord hρ j) j).continuous)
    (fun j _ => hasCompactSupport_dcoord (hasCompactSupport_dcoord hc j) j) x
  have hlap : (lapCS S ρ) = fun y => ∑ i ∈ S, dcoord i (dcoord i ρ) y := rfl
  simp only [lapCS]
  rw [hlap, hsum]
  exact Finset.sum_congr rfl fun j _ => congrFun (hd j) x
