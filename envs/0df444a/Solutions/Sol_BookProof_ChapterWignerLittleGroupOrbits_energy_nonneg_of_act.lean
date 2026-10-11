-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.energy_nonneg_of_act
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:42.616723+00:00
-- url     : https://prove2.me/submissions/ce8a1049-37a4-475e-b5c1-8275954099f7

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.energy_nonneg_of_act
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_posSemidef
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_trace
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : Fin 4 → ℝ}
    (hp0 : 0 ≤ p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2)
    (h : act A (hermOfMom p) = hermOfMom q) : 0 ≤ q 0 := by

  have hpsd : (hermOfMom q).PosSemidef := by
    rw [← h, act]
    exact (hermOfMom_posSemidef hp0 hmass).mul_mul_conjTranspose_same A
  have htr : (0 : ℂ) ≤ ((2 * q 0 : ℝ) : ℂ) := by
    have := hpsd.trace_nonneg
    rwa [hermOfMom_trace] at this
  have : (0 : ℝ) ≤ 2 * q 0 := Complex.zero_le_real.mp htr
  linarith
