-- Prove2me | solution 1 for CompactnessConjecture.symplecticLineGraphMap_coordinate_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/26fc901a-0a7c-4d17-add5-8acaefddf61e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (z : Fin 2 → K) (i : Fin 2) :
    symplecticLineGraphMap K L hvertical z i =
      symplecticLineGraphMap K L hvertical ![1, 0] i * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] i * z 1 := by
  have hz : z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    funext j
    fin_cases j <;> simp [smul_eq_mul]
  calc
    symplecticLineGraphMap K L hvertical z i =
        symplecticLineGraphMap K L hvertical
          (z 0 • ![1, 0] + z 1 • ![0, 1]) i := by
      rw [← hz]
    _ = symplecticLineGraphMap K L hvertical ![1, 0] i * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] i * z 1 := by
      rw [map_add, map_smul, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
end CompactnessConjecture
