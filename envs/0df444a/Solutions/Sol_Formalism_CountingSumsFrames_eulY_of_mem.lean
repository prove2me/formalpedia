-- Prove2me | solution 1 for Formalism.CountingSumsFrames.eulY_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:40.518345+00:00
-- url     : https://prove2.me/submissions/a3bdce5a-45e4-4e86-915b-36fbaaa4863a

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_eulY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable (K : Type) [Field K] (k : ℕ)
variable {K k}
namespace Formalism.CountingSumsFrames
theorem _root_.solution {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    eulY K k f = (B : K) • f := by
  ext m
  rw [coeff_eulY, coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ f.support
  · rw [(hf m hm).2]
  · rw [notMem_support_iff.1 hm]; simp
end Formalism.CountingSumsFrames
