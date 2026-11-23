-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.exists_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:32.312145+00:00
-- url     : https://prove2.me/submissions/a4242dcb-fab1-47ba-8f30-37037bf6d7be

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_PolAB_iff
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_hXY_mem_PolAB

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
open Formalism.CountingSumsFrames.Har4
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open DirectSum
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {K : Type} [Field K] {k A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) {w G : PolXY K k}
    (hw : w ∈ PolAB K k A B) (h : w = hXY K k * G) :
    ∃ G' ∈ PolAB K k (A - 1) (B - 1), w = hXY K k * G' := by
  classical
  let 𝒜 := weightedHomogeneousSubmodule K (wXY k)
  have hh : hXY K k ∈ 𝒜 (1, 1) := (mem_PolAB_iff _).1 hXY_mem_PolAB
  have hw' : w ∈ 𝒜 (A, B) := (mem_PolAB_iff _).1 hw
  refine ⟨(decompose 𝒜 G (A - 1, B - 1) : PolXY K k), (mem_PolAB_iff _).2 (decompose 𝒜 G (A - 1, B - 1)).2, ?_⟩
  rw [← DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hh, ← h]
  have : ((1, 1) + (A - 1, B - 1) : ℕ × ℕ) = (A, B) := by
    ext <;> simp <;> omega
  rw [this, DirectSum.decompose_of_mem_same 𝒜 hw']
end Formalism.CountingSumsFrames.Har4
