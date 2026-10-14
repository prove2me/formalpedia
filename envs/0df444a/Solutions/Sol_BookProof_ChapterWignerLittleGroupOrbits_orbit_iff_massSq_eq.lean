-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.orbit_iff_massSq_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:38.924124+00:00
-- url     : https://prove2.me/submissions/fa6f1815-7e97-497d-a076-c968d3630eab

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.orbit_iff_massSq_eq
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_act_inv_of_act
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_det_inv_eq_one
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_mul
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_exists_boost_massive
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_exists_boost_null
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_mass_invariant
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution {p q : Fin 4 → ℝ} (hp0 : 0 < p 0) (hq0 : 0 < q 0)
    (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) :
    (∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom p) = hermOfMom q) ↔
      q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := by

  constructor
  · rintro ⟨A, hA, h⟩
    exact mass_invariant hA h
  · intro hsq
    -- both are boosts of the same reference momentum
    rcases eq_or_lt_of_le hmass with hnull | hmassive
    · obtain ⟨A₁, hA₁, h₁⟩ := exists_boost_null p hp0 (by linarith)
      obtain ⟨A₂, hA₂, h₂⟩ := exists_boost_null q hq0 (by linarith [hsq])
      refine ⟨A₂ * A₁⁻¹, by rw [Matrix.det_mul, hA₂, det_inv_eq_one hA₁]; ring, ?_⟩
      rw [act_mul, act_inv_of_act hA₁ h₁, h₂]
    · set m : ℝ := Real.sqrt (p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) with hm
      have hmpos : 0 < m := Real.sqrt_pos.2 hmassive
      have hm2 : m ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := Real.sq_sqrt (le_of_lt hmassive)
      obtain ⟨A₁, hA₁, h₁⟩ := exists_boost_massive hmpos p hp0 hm2.symm
      obtain ⟨A₂, hA₂, h₂⟩ := exists_boost_massive hmpos q hq0 (by rw [hsq]; exact hm2.symm)
      refine ⟨A₂ * A₁⁻¹, by rw [Matrix.det_mul, hA₂, det_inv_eq_one hA₁]; ring, ?_⟩
      rw [act_mul, act_inv_of_act hA₁ h₁, h₂]
