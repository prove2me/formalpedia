-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.har_of_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:44.052802+00:00
-- url     : https://prove2.me/submissions/54fe65f8-9aeb-4b9e-b844-b0a4155b47df

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_zero_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
private theorem mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero {A B : ℕ} {f : PolXY K k} :
    f ∈ HarAB K k A B ↔ f ∈ PolAB K k A B ∧ ctrF K k f = 0 := Iff.rfl
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution {A : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A 0) : f ∈ HarAB K k A 0 := by
  exact mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.2 ⟨hf, ctrF_zero_right hf⟩
end Formalism.CountingSumsFrames.Har2
