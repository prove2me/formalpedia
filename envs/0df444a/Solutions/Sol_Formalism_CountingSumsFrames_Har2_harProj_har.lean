-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.harProj_har
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:11.040822+00:00
-- url     : https://prove2.me/submissions/a78652b3-361f-4357-9533-6528abd8745b

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_cPoint_zero
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_apply
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
theorem _root_.solution {A B : ℕ} {f : PolXY K k} (hf : f ∈ HarAB K k A B) : harProj K k A B f = f := by
  obtain ⟨_, h2⟩ := mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hf
  have hz : ∀ l : ℕ, cP K (A + B + k - 2) (l + 1) • (hXY K k ^ (l + 1) * (ctrF K k ^ (l + 1)) f) = 0 :=
    fun l => by rw [pow_succ (ctrF K k), Module.End.mul_apply, h2, map_zero, mul_zero, smul_zero]
  rw [harProj_apply, Finset.sum_range_succ']
  simp [hz, cPoint_zero]
end Formalism.CountingSumsFrames.Har2
