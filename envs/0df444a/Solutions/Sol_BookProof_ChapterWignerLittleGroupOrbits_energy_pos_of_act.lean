-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.energy_pos_of_act
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:36.863766+00:00
-- url     : https://prove2.me/submissions/cb6d46f6-7e9d-425a-99b8-71c58debf4c7

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.energy_pos_of_act
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_eq_zero_iff
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_act_inv_of_act
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_energy_nonneg_of_act
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_mass_invariant
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ}
    (hp0 : 0 < p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2)
    (h : act A (hermOfMom p) = hermOfMom q) : 0 < q 0 := by

  have hnn : 0 ≤ q 0 := energy_nonneg_of_act (le_of_lt hp0) hmass h
  rcases eq_or_lt_of_le hnn with hzero | hpos
  · -- `q⁰ = 0` and `q·q ≥ 0` force `q = 0`, hence `p = 0`, contradicting `p⁰ > 0`
    exfalso
    have hq : q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 :=
      mass_invariant hA h
    have hq0 : q 0 = 0 := hzero.symm
    have hzeroes : ∀ i, q i = 0 := by
      have hle : q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 ≤ 0 := by nlinarith [hq, hmass, hq0]
      have h1' : q 1 = 0 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
      have h2' : q 2 = 0 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
      have h3' : q 3 = 0 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
      intro i
      fin_cases i
      · simpa using hq0
      · simpa using h1'
      · simpa using h2'
      · simpa using h3'
    have hqzero : hermOfMom q = 0 := hermOfMom_eq_zero_iff.2 hzeroes
    -- invert the action
    have hp : hermOfMom p = 0 := by
      have hback := act_inv_of_act hA h
      rw [hqzero, act, Matrix.mul_zero, Matrix.zero_mul] at hback
      exact hback.symm
    have := (hermOfMom_eq_zero_iff.1 hp) 0
    linarith
  · exact hpos
