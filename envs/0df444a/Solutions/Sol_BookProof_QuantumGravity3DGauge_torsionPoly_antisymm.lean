-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.torsionPoly_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T05:10:30.088422+00:00
-- url     : https://prove2.me/submissions/49251d27-c22d-427f-8d11-e42075e37b41

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge
open MvPolynomial

theorem solution (mu nu a : Fin 4) :
    torsionPoly mu nu a = -torsionPoly nu mu a := by
  simp [torsionPoly, neg_sub]
