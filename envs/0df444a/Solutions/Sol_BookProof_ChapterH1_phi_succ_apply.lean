-- Prove2me | solution 1 for BookProof.ChapterH1.phi_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:18:48.683351+00:00
-- url     : https://prove2.me/submissions/1607445f-b7b8-4570-95fb-2bcaef1301ec

-- Generated from ChapterH1.lean — solution of BookProof.ChapterH1.phi_succ_apply
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1







open scoped BigOperators
open intervalIntegral


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (z : ℂ) :
    phi (k + 1) z = ∫ s in (0 : ℝ)..1, Complex.exp (s * z) * (1 - s) ^ k / k.factorial := rfl
