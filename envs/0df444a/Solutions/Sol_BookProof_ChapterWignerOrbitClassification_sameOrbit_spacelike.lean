-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.sameOrbit_spacelike
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:23.238471+00:00
-- url     : https://prove2.me/submissions/829721f3-46e0-4b90-99a9-ebfe73ad844c

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.sameOrbit_spacelike
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_SameOrbit_symm
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_SameOrbit_trans
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_exists_boost_spacelike
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution {p q : Fin 4 → ℝ} (hneg : minkSq p < 0) (hpq : minkSq p = minkSq q) :
    SameOrbit p q := by

  set m : ℝ := Real.sqrt (-minkSq p) with hm
  have hmpos : 0 < m := Real.sqrt_pos.2 (by linarith)
  have hm2 : m ^ 2 = -minkSq p := Real.sq_sqrt (by linarith)
  have hp : minkSq p = -m ^ 2 := by rw [hm2]; ring
  have hq : minkSq q = -m ^ 2 := by rw [← hpq]; exact hp
  have h1 : SameOrbit (spaceRefMom m) p := exists_boost_spacelike hmpos p hp
  have h2 : SameOrbit (spaceRefMom m) q := exists_boost_spacelike hmpos q hq
  exact h1.symm.trans h2
