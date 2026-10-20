-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bookConstraintAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T23:28:49.881934+00:00
-- url     : https://prove2.me/submissions/0a630fa8-e5da-4064-af0f-baea9c083c11

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.bookConstraintAlgebra
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_ghostOpN_comm
import Theorems.Thm_BookProof_BookBrstYangMills_gaussGen_bracket
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterYangMillsGhostSector
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.YangMillsGhost

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in

theorem solution : ConstraintAlgebra G.f (gaussGen G) chiOp betaOp where
  comm_chi _ _ := bosOpN_ghostOpN_comm _ _
  comm_beta _ _ := bosOpN_ghostOpN_comm _ _
  bracket a b := gaussGen_bracket G a b
