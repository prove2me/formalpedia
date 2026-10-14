-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.orbit_classification
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:54:36.570519+00:00
-- url     : https://prove2.me/submissions/e18eb901-5adf-46b9-aa03-fac9781ac7fa

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.orbit_classification
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_minkSq_eq_of_sameOrbit
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_sameOrbit_spacelike
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_sameOrbit_negMom
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_negMom_negMom
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_eq_zero_of_energy_zero
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_sameOrbit_of_zero
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_energy_pos_of_act
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_eq_zero_iff
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_orbit_iff_massSq_eq
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution (p q : Fin 4 → ℝ) :
    SameOrbit p q ↔ minkSq p = minkSq q ∧
      (minkSq p < 0 ∨ ((∀ i, p i = 0) ∧ (∀ i, q i = 0)) ∨ (0 < p 0 ∧ 0 < q 0) ∨
        (p 0 < 0 ∧ q 0 < 0)) := by

  constructor
  · intro h
    refine ⟨minkSq_eq_of_sameOrbit h, ?_⟩
    rcases lt_or_ge (minkSq p) 0 with hneg | hmass
    · exact Or.inl hneg
    · rcases lt_trichotomy (p 0) 0 with hlt | heq | hgt
      · -- negative energy: pass to the negated momenta, which are future-pointing
        obtain ⟨A, hA, hact⟩ := sameOrbit_negMom h
        have hp0 : 0 < negMom p 0 := by simp [negMom]; linarith
        have hmass' : 0 ≤ negMom p 0 ^ 2 - negMom p 1 ^ 2 - negMom p 2 ^ 2 - negMom p 3 ^ 2 := by
          have := hmass
          simp only [minkSq] at this
          simpa [negMom] using this
        have := energy_pos_of_act hA hp0 hmass' hact
        simp only [negMom] at this
        exact Or.inr (Or.inr (Or.inr ⟨hlt, by linarith⟩))
      · -- zero energy and nonnegative square: both momenta vanish
        have hpz : ∀ i, p i = 0 := eq_zero_of_energy_zero hmass heq
        obtain ⟨A, hA, hact⟩ := h
        have hqz : hermOfMom q = 0 := by
          rw [← hact, hermOfMom_eq_zero_iff.2 hpz, act, Matrix.mul_zero, Matrix.zero_mul]
        exact Or.inr (Or.inl ⟨hpz, hermOfMom_eq_zero_iff.1 hqz⟩)
      · obtain ⟨A, hA, hact⟩ := h
        have hmass' : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := hmass
        exact Or.inr (Or.inr (Or.inl ⟨hgt, energy_pos_of_act hA hgt hmass' hact⟩))
  · rintro ⟨hsq, hcase⟩
    rcases lt_or_ge (minkSq p) 0 with hneg | hmass
    · exact sameOrbit_spacelike hneg hsq
    rcases hcase with hneg | ⟨hpz, hqz⟩ | ⟨hp0, hq0⟩ | ⟨hp0, hq0⟩
    · exact absurd hneg (not_lt.2 hmass)
    · exact sameOrbit_of_zero hpz hqz
    · have hmass' : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := hmass
      have hsq' : q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 :=
        hsq.symm
      exact (orbit_iff_massSq_eq hp0 hq0 hmass').2 hsq'
    · -- both of negative energy: negate, apply the future-cone case, negate back
      have hp0' : 0 < negMom p 0 := by simp [negMom]; linarith
      have hq0' : 0 < negMom q 0 := by simp [negMom]; linarith
      have hmass' : 0 ≤ negMom p 0 ^ 2 - negMom p 1 ^ 2 - negMom p 2 ^ 2 - negMom p 3 ^ 2 := by
        have := hmass
        simp only [minkSq] at this
        simpa [negMom] using this
      have hsq' : negMom q 0 ^ 2 - negMom q 1 ^ 2 - negMom q 2 ^ 2 - negMom q 3 ^ 2
          = negMom p 0 ^ 2 - negMom p 1 ^ 2 - negMom p 2 ^ 2 - negMom p 3 ^ 2 := by
        have h := hsq.symm
        simp only [minkSq] at h
        simpa [negMom] using h
      have hnn : SameOrbit (negMom p) (negMom q) := (orbit_iff_massSq_eq hp0' hq0' hmass').2 hsq'
      have := sameOrbit_negMom hnn
      rwa [negMom_negMom, negMom_negMom] at this
