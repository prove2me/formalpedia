-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.hermiteCoreOp_deficiencyTrivialAt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:45:03.53562+00:00
-- url     : https://prove2.me/submissions/d7241ca1-2fa2-41b6-b3e4-cbfbb56b4c63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.hermiteCoreOp_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteStrichartzQG_inner_hermiteLp_eq_zero_iff
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteLp_mem_hermiteCore
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_hermiteLp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized
open BookProof.HermiteCore

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt hermiteCore (hermiteCoreOp lam) z := by

  intro w hw
  refine inner_hermiteLp_eq_zero_iff.mp fun n => ?_
  have h := hw ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩
  rw [hermiteCoreOp_hermiteLp, inner_smul_left] at h
  have hconj : (starRingEnd ℂ) ((lam n : ℂ)) = (lam n : ℂ) := Complex.conj_ofReal _
  rw [hconj] at h
  have hne : ((lam n : ℂ)) - z ≠ 0 := by
    intro hc
    have : z = ((lam n : ℝ) : ℂ) := by linear_combination -hc
    rw [this] at hz
    simp at hz
  have hprod : (((lam n : ℂ)) - z) * (inner ℂ (hermiteLp n) w : ℂ) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hprod).resolve_left hne
