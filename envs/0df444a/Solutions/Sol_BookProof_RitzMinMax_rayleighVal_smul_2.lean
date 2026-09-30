-- Prove2me | solution 2 for BookProof.RitzMinMax.rayleighVal_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T18:32:34.568583+00:00
-- url     : https://prove2.me/submissions/749813c2-f082-4682-bc7b-ed074662ebf0

-- Generated from ChapterSirkRitzMinMax.lean — solution of BookProof.RitzMinMax.rayleighVal_smul
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax










noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (c : ℂ) (x : F) :
    rayleighVal T (c • x) = ‖c‖ ^ 2 * rayleighVal T x := by

  have h : (inner ℂ (c • x) (T (c • x)) : ℂ) = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ x (T x) := by
    rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
    congr 1
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [rayleighVal, rayleighVal, h, Complex.re_ofReal_mul]
