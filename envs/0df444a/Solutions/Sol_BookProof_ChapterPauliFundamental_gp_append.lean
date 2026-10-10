-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.gp_append
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:04.338727+00:00
-- url     : https://prove2.me/submissions/8a0d2d93-813a-4833-8d56-090a9b92441f

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.gp_append
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

set_option maxHeartbeats 1000000 in
theorem solution (A : Fin 4 → M4) (l₁ l₂ : List (Fin 4)) :
    gp A (l₁ ++ l₂) = gp A l₁ * gp A l₂ := by

  induction l₁ with
  | nil => simp [gp]
  | cons a t ih => simp [gp, ih, mul_assoc]
