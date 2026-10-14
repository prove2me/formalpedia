-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.future_cone_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:37.822818+00:00
-- url     : https://prove2.me/submissions/dc10574e-8f1a-4030-9f03-d50349a72ebc

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.future_cone_invariant
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_energy_pos_of_act
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_mass_invariant
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ}
    (hp0 : 0 < p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2)
    (h : act A (hermOfMom p) = hermOfMom q) :
    0 < q 0 ∧ q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := ⟨energy_pos_of_act hA hp0 hmass h, mass_invariant hA h⟩
