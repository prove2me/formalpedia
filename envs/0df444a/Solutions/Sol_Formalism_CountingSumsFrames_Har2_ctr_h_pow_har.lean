-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctr_h_pow_har
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:20.646804+00:00
-- url     : https://prove2.me/submissions/d9e8676e-76af-4d75-913f-140acc4178ea

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_h_pow
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
theorem _root_.solution {a b : ℕ} (i : ℕ) {w : PolXY K k} (hw : w ∈ HarAB K k a b) :
    ctrF K k (hXY K k ^ (i + 1) * w) = (((i + 1) * (a + b + k + i) : ℕ) : K) • (hXY K k ^ i * w) := by
  rw [ctr_h_pow i (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hw).1, (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hw).2, mul_zero, zero_add]
end Formalism.CountingSumsFrames.Har2
