-- Prove2me | solution 1 for BookProof.ChapterA3.toC_mgammaR
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:27:16.960577+00:00
-- url     : https://prove2.me/submissions/fe874db3-02c3-4cc6-89a0-3268fec5c431

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

theorem solution (μ : Fin 4) : toC (mgammaR μ) = mgamma μ := by
  ext i j
  simp [toC, mgammaR, mgamma]

#print axioms solution
