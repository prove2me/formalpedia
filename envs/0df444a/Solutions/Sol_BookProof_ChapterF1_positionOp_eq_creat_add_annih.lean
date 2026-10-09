-- Prove2me | solution 1 for BookProof.ChapterF1.positionOp_eq_creat_add_annih
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:55:00.533262+00:00
-- url     : https://prove2.me/submissions/95844f76-5cec-4405-a317-50e38a532bee

-- Generated from ChapterF1.lean — solution of BookProof.ChapterF1.positionOp_eq_creat_add_annih
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1



open Polynomial Finset
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : positionOp = creat + annih := rfl
