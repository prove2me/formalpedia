-- Prove2me | solution 1 for BookProof.ChapterH9.norm_compress_mono
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:33:05.027568+00:00
-- url     : https://prove2.me/submissions/e98b8d0e-f9c0-4e5a-9133-6cf89bbf8b96

import Definitions.Def_ChapterH4

open BookProof.ChapterH4 ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hJiso : ∀ x : F, ‖J x‖ = ‖x‖) :
    ‖compress Vn X‖ ≤ ‖compress Vm X‖ := by
  have hc : compress Vn X = compress J (compress Vm X) := by
    simp only [hJ, compress, adjoint_comp, comp_assoc]
  rw [hc]
  have hnorm : ‖J‖ ≤ 1 := J.opNorm_le_bound zero_le_one
    (by simpa only [one_mul] using fun x => (hJiso x).le)
  have hadj : ‖adjoint J‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hnorm
  change ‖(adjoint J).comp ((compress Vm X).comp J)‖ ≤ ‖compress Vm X‖
  calc
    _ ≤ ‖adjoint J‖ * ‖(compress Vm X).comp J‖ := (adjoint J).opNorm_comp_le _
    _ ≤ 1 * (‖compress Vm X‖ * 1) := mul_le_mul hadj
      (((compress Vm X).opNorm_comp_le J).trans
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)))
      (norm_nonneg _) zero_le_one
    _ = ‖compress Vm X‖ := by simp only [one_mul, mul_one]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
