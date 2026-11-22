-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.levelProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:22.837433+00:00
-- url     : https://prove2.me/submissions/648a3e1c-764c-4545-b209-ffa3ac4879f5

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds

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
theorem _root_.solution (A B j : ℕ) (f : PolXY K k) : levelProj K k A B j f =
    hXY K k ^ j * (((((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)⁻¹ * ((j.factorial : ℕ) : K)⁻¹) •
      harProj K k (A - j) (B - j) (ctrDiv K k j f)) := by
  simp only [levelProj, LinearMap.smul_apply, LinearMap.comp_apply, hDiv, LinearMap.mulLeft_apply,
    mul_smul_comm, smul_smul]
end Formalism.CountingSumsFrames.Har2
