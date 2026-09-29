-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.realCoeff_torsionPoly
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T05:51:12.144152+00:00
-- url     : https://prove2.me/submissions/b0045318-2a5e-41cb-b905-2df3501ae967

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge
open BookProof.YangMillsHermite
open MvPolynomial

theorem solution (mu nu a : Fin 4) : RealCoeff (torsionPoly mu nu a) := by
  simp [RealCoeff, torsionPoly, starP, map_sub, map_X]
