-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.ctrF_mem_PolAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:33.872991+00:00
-- url     : https://prove2.me/submissions/69e5fa57-fe6c-4e50-bbe3-b1e4aafeba63

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xDeg_add
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yDeg_add
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xDeg_single_inl
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_xDeg_single_inr
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yDeg_single_inl
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_yDeg_single_inr
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_coeff_ctrF
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_xDeg_add
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_yDeg_add


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
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {a b : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    ctrF K k f ∈ PolAB K k (a - 1) (b - 1) := by
  show ∀ m ∈ (ctrF K k f).support, xDeg m = a - 1 ∧ yDeg m = b - 1
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_ctrF] at hm
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hc : coeff (m + Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1) f ≠ 0 := by
    intro h0
    apply hi
    rw [h0]
    ring
  have hf' := (show ∀ m ∈ f.support, xDeg m = a ∧ yDeg m = b from hf) _ (MvPolynomial.mem_support_iff.2 hc)
  rw [xDeg_add, xDeg_add, yDeg_add, yDeg_add, xDeg_single_inl, xDeg_single_inr, yDeg_single_inl,
    yDeg_single_inr] at hf'
  omega
end Formalism.CountingSumsFrames.Har4
