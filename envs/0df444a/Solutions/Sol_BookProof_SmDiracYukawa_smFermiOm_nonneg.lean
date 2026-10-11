-- Prove2me | solution 1 for BookProof.SmDiracYukawa.smFermiOm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:59.387971+00:00
-- url     : https://prove2.me/submissions/fdb5c5dc-8c14-4c28-9307-e4fe85e23d6b

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.smFermiOm_nonneg
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
variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) : 0 ≤ smFermiOm om c0 := by

  have : 0 ≤ ∑ i : Fin n, om i := Finset.sum_nonneg fun i _ => hom i
  simp only [smFermiOm]
  linarith
