-- Prove2me | solution 1 for BookProof.YangMillsFriedrichsLimit.sirk_limit_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:12.558755+00:00
-- url     : https://prove2.me/submissions/68b60ccd-beb4-46d5-ac69-47135b0075bf

-- Generated from ChapterYangMillsFriedrichsLimit.lean — solution of BookProof.YangMillsFriedrichsLimit.sirk_limit_unique
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterFarisLavine
open BookProof.YangMillsFriedrichsLimit









open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open scoped InnerProductSpace ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]







open BookProof.ChapterH5 BookProof.ChapterH9

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (A B : F →L[ℂ] F) (v : F)
    (hdense : Dense ((⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F) : Set F))
    (hagree : ∀ x ∈ (⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F), A x = B x) :
    A = B := by

  ext u
  have := Continuous.ext_on hdense A.continuous B.continuous (fun x hx => hagree x hx)
  exact congrFun this u
