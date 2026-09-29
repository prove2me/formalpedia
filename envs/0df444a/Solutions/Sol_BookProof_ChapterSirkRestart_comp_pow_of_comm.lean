-- Prove2me | solution 1 for BookProof.ChapterSirkRestart.comp_pow_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:53:39.807522+00:00
-- url     : https://prove2.me/submissions/9e055bd1-41ba-4dfc-a064-f81e0cff4f03

-- Generated from ChapterSirkRestart.lean — solution of BookProof.ChapterSirkRestart.comp_pow_of_comm
import Mathlib
import Definitions.Def_ChapterSirkRestart
open BookProof.ChapterSirkRestart








noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (U Om : E →L[ℂ] E) (hcomm : Om.comp U = U.comp Om) (n : ℕ) :
    Om.comp (U ^ n) = (U ^ n).comp Om := by

  induction n with
  | zero => ext w; simp
  | succ n ih =>
    have hpow : (U ^ (n + 1)) = U.comp (U ^ n) := by
      rw [pow_succ']; rfl
    ext w
    have h1 : Om (U ((U ^ n) w)) = U (Om ((U ^ n) w)) :=
      congrArg (fun f : E →L[ℂ] E => f ((U ^ n) w)) hcomm
    have h2 : Om ((U ^ n) w) = (U ^ n) (Om w) :=
      congrArg (fun f : E →L[ℂ] E => f w) ih
    simp only [hpow, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [h1, h2]
