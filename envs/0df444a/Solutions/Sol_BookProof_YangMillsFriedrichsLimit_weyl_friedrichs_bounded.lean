-- Prove2me | solution 1 for BookProof.YangMillsFriedrichsLimit.weyl_friedrichs_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:54.135598+00:00
-- url     : https://prove2.me/submissions/b0e6b841-5e27-4138-9ea5-9f34ae4ca2c9

-- Generated from ChapterYangMillsFriedrichsLimit.lean — solution of BookProof.YangMillsFriedrichsLimit.weyl_friedrichs_bounded
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Theorems.Thm_BookProof_YangMillsFriedrichsLimit_sirk_limit_eq_positive_selfadjoint_extension
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









open BookProof.ChapterH5 BookProof.ChapterH9

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace F] {D : Submodule ℂ F} {n m : ℕ}
    {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D}
    (hdense : Dense (D : Set F))
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a)))
    (C : ℝ) (hbd : ∀ x : D, ‖weylOp pi Bf x‖ ≤ C * ‖(x : F)‖) (v : F) :
    ∃ A : F →L[ℂ] F,
      (∀ x : D, A (x : F) = weylOp pi Bf x) ∧
      IsPositiveSelfAdjointExtension (weylOp pi Bf) (topRestrict A) ∧
      (Dense ((⨆ k : ℕ, krylovSpan A.toLinearMap v k : Submodule ℂ F) : Set F) →
        ∀ u : F, Filter.Tendsto (fun k : ℕ => sirkCompression A v k u)
          Filter.atTop (nhds (A u))) := by

  obtain ⟨A, hagree, hext, hlim⟩ :=
    sirk_limit_eq_positive_selfadjoint_extension (weylOp pi Bf) hdense
      (weylOpDom_symmetricOn hpi hB) (weylOpDom_quadForm_nonneg hpi hB) C hbd v
  exact ⟨A, hagree, hext, fun hcyc => (hlim hcyc).1⟩
