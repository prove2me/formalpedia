-- Prove2me | solution 1 for BookProof.ConvolutionCalc.hasCompactSupport_finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T09:20:54.930814+00:00
-- url     : https://prove2.me/submissions/af49fda0-682e-4621-93c5-c9245bd70d95

-- Generated from ChapterConvolutionCalc.lean — solution of BookProof.ConvolutionCalc.hasCompactSupport_finsetSum
import Mathlib
import Definitions.Def_ChapterConvolutionCalc
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
theorem solution {ι : Type*} (s : Finset ι) {f : ι → Vd d → ℂ}
    (h : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by

  classical
  induction s using Finset.induction with
  | empty =>
      have hz : HasCompactSupport (fun _ : Vd d => (0 : ℂ)) := HasCompactSupport.zero
      convert hz using 1
      funext x; simp
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))
