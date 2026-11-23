-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.h_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:44.489437+00:00
-- url     : https://prove2.me/submissions/965e4629-8498-47da-9d35-99e33b0fc792

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_X_inl_mul_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_X_inr_mul_mem

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
theorem _root_.solution {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    hXY K k * f ∈ PolAB K k (A + 1) (B + 1) := by
  simp only [hXY, Finset.sum_mul]
  exact Submodule.sum_mem _ fun i _ => by
    rw [mul_assoc]; exact X_inl_mul_mem i (X_inr_mul_mem i hf)
end Formalism.CountingSumsFrames.Har2
