-- Prove2me | solution 1 for BookProof.BookBrstYangMills.gaussGen_bracket
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:29:56.886268+00:00
-- url     : https://prove2.me/submissions/19512803-6ec8-4059-8218-ddd98f80f641

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.gaussGen_bracket
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_mul
import Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_sub
import Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_rsmul
import Theorems.Thm_BookProof_BookBrstYangMills_bosOpN_sum
import Theorems.Thm_BookProof_BookBrstYangMills_gaussGenPoly_bracket
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (c e : Fin N) :
    gaussGen G c * gaussGen G e - gaussGen G e * gaussGen G c
      = ∑ h, (G.f c e h) • gaussGen G h := by

  rw [gaussGen, gaussGen, ← bosOpN_mul, ← bosOpN_mul, ← bosOpN_sub, gaussGenPoly_bracket,
    bosOpN_sum]
  exact Finset.sum_congr rfl fun h _ => bosOpN_rsmul _ _
