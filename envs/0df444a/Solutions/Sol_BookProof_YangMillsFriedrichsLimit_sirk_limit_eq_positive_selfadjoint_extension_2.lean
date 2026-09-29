-- Prove2me | solution 2 for BookProof.YangMillsFriedrichsLimit.sirk_limit_eq_positive_selfadjoint_extension
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:33:42.141653+00:00
-- url     : https://prove2.me/submissions/0bbd0ae7-e964-41aa-92d2-734a928849d4

-- Generated from ChapterYangMillsFriedrichsLimit.lean — solution of BookProof.YangMillsFriedrichsLimit.sirk_limit_eq_positive_selfadjoint_extension
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Theorems.Thm_BookProof_YangMillsFriedrichsLimit_friedrichs_of_bounded
import Theorems.Thm_BookProof_YangMillsFriedrichsLimit_sirk_compression_tendsto
import Theorems.Thm_BookProof_YangMillsFriedrichsLimit_sirk_limit_unique
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
theorem solution [CompleteSpace F] {D : Submodule ℂ F}
    (H : D →ₗ[ℂ] F) (hdenseD : Dense (D : Set F)) (hsym : SymmetricOn D H)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) (C : ℝ) (hbd : ∀ x : D, ‖H x‖ ≤ C * ‖(x : F)‖) (v : F) :
    ∃ A : F →L[ℂ] F,
      (∀ x : D, A (x : F) = H x) ∧
      IsPositiveSelfAdjointExtension H (topRestrict A) ∧
      (Dense ((⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F) : Set F) →
        (∀ u : F, Filter.Tendsto (fun n : ℕ => sirkCompression A v n u)
          Filter.atTop (nhds (A u)))
        ∧ ∀ B : F →L[ℂ] F,
            (∀ x ∈ (⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F), A x = B x) →
            A = B) := by

  obtain ⟨A, hagree, hext⟩ := friedrichs_of_bounded H hdenseD hsym hpos C hbd
  exact ⟨A, hagree, hext, fun hcyc =>
    ⟨fun u => sirk_compression_tendsto A v hcyc u, fun B hB => sirk_limit_unique A B v hcyc hB⟩⟩
