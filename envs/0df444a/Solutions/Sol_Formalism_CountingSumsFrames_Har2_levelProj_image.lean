-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.levelProj_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:50.539795+00:00
-- url     : https://prove2.me/submissions/574e6d41-3396-417e-b457-a0075cf65678

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_apply
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrDiv_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution [CharZero K] (hk : 1 ≤ k) {A B : ℕ} (j : ℕ) {f : PolXY K k}
    (hf : f ∈ PolAB K k A B) :
    ∃ w ∈ HarAB K k (A - j) (B - j), levelProj K k A B j f = hXY K k ^ j * w := by
  exact ⟨((((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)⁻¹ * ((j.factorial : ℕ) : K)⁻¹) •
    harProj K k (A - j) (B - j) (ctrDiv K k j f),
    Submodule.smul_mem _ _ (harProj_mem hk (ctrDiv_mem j hf)), levelProj_apply A B j f⟩
end Formalism.CountingSumsFrames.Har2
