-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:38.72083+00:00
-- url     : https://prove2.me/submissions/1b10ef32-7606-44e9-8172-e1612c1739a5

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_posSemidef
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_eq_zero_iff
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_posSemidef_diag2
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_exists_boost_massive
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_exists_boost_null
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_nullMom
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_restMom
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin 4 → ℝ} (hp0 : 0 ≤ p 0)
    (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) :
    (hermOfMom p).PosSemidef := by

  rcases eq_or_lt_of_le hp0 with hzero | hpos
  · -- `p⁰ = 0` forces `p = 0`
    have hp : ∀ i, p i = 0 := by
      have h1 : p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 ≤ 0 := by nlinarith [hmass, hzero]
      have h1' : p 1 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
      have h2' : p 2 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
      have h3' : p 3 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
      intro i
      fin_cases i
      · simpa using hzero.symm
      · simpa using h1'
      · simpa using h2'
      · simpa using h3'
    rw [hermOfMom_eq_zero_iff.2 hp]
    exact Matrix.PosSemidef.zero
  · rcases eq_or_lt_of_le hmass with hnull | hmassive
    · -- lightlike: reduce to `diag(2, 0)`
      obtain ⟨A, _, hA⟩ := exists_boost_null p hpos (by linarith)
      rw [← hA, act, hermOfMom_nullMom]
      have h2 : (!![(2 : ℂ), 0; 0, 0]) = !![((2 : ℝ) : ℂ), 0; 0, ((0 : ℝ) : ℂ)] := by
        norm_num
      rw [h2]
      exact (posSemidef_diag2 (by norm_num) le_rfl).mul_mul_conjTranspose_same A
    · -- massive: reduce to `diag(m, m)`
      set m : ℝ := Real.sqrt (p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) with hm
      have hmpos : 0 < m := Real.sqrt_pos.2 hmassive
      have hm2 : m ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := Real.sq_sqrt (le_of_lt hmassive)
      obtain ⟨A, _, hA⟩ := exists_boost_massive hmpos p hpos hm2.symm
      have hdiag : ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = !![(m : ℂ), 0; 0, (m : ℂ)] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [← hA, act, hermOfMom_restMom, hdiag]
      exact (posSemidef_diag2 (le_of_lt hmpos) (le_of_lt hmpos)).mul_mul_conjTranspose_same A
