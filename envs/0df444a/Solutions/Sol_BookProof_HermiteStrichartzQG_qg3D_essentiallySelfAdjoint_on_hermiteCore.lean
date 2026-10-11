-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.qg3D_essentiallySelfAdjoint_on_hermiteCore
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:07.381543+00:00
-- url     : https://prove2.me/submissions/ab53fbff-b058-4cf0-a11f-49897f91a04f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.qg3D_essentiallySelfAdjoint_on_hermiteCore
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) :
    EssentiallySelfAdjointOn hermiteCore (qg3DHermiteHamiltonian xi xiY V) := hermiteCoreOp_essentiallySelfAdjoint _
