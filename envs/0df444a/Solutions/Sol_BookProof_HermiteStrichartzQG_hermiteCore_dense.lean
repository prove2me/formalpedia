-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.hermiteCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:11:59.159788+00:00
-- url     : https://prove2.me/submissions/89282727-a76b-4147-80dd-953c20d7fe20

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.hermiteCore_dense
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution : Dense (hermiteCore : Set L2R) := by

  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact top_le_iff.mp hermiteLp_span_dense
