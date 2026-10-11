-- Prove2me | solution 1 for BookProof.SmDiracYukawa.smFermiWeight_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:24.088394+00:00
-- url     : https://prove2.me/submissions/adf6a9bd-fad7-4d23-be53-1498447be84e

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.smFermiWeight_ge_one
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (S : Finset (Fin n)) : 1 ≤ smFermiWeight om c0 S := by

  have : 0 ≤ ∑ i ∈ S, om i := Finset.sum_nonneg fun i _ => hom i
  simp only [smFermiWeight]
  linarith
