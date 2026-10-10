-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.cliff_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:06.388213+00:00
-- url     : https://prove2.me/submissions/9285c7f7-f1a2-4234-b7b0-01cbb0236925

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.cliff_sq
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (hA : IsCliffordC A) (μ : Fin 4) :
    A μ * A μ = (if μ = 0 then (-1 : ℂ) else 1) • (1 : M4) := by

  have h := hA μ μ
  have h2 : (2 : ℂ) • (A μ * A μ) = (-2 * minkowski μ μ) • (1 : M4) := by
    rw [two_smul]; exact h
  have h3 := congrArg (fun Y : M4 => (2 : ℂ)⁻¹ • Y) h2
  simp only [smul_smul] at h3
  rw [show (2 : ℂ)⁻¹ * 2 = 1 by norm_num, one_smul] at h3
  rw [h3]; congr 1
  by_cases h0 : μ = 0 <;> simp [minkowski, minkowskiZ, h0]
