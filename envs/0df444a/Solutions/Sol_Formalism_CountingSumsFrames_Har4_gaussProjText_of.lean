-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.gaussProjText_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:44.522727+00:00
-- url     : https://prove2.me/submissions/9b2538c9-1f73-4db2-84fb-aca1f6994389

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_smul_mem_latOf_gauss
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_smul_mem_latOf_dual
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_exponent_le

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
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution (H : GaussProj) : GaussProjText := by
  intro K _ _ k A B a p e R g hk hp hR hA hB he f hf j hj
  have hE := exponent_le hk hp hA hB he
  have hpe : (p : K) ^ e = (p : K) ^ (e - (k + 1) * Nat.log p (A + B + k)) *
      (p : K) ^ ((k + 1) * Nat.log p (A + B + k)) := by
    rw [← pow_add, Nat.sub_add_cancel hE]
  have hmem : (p : K) ^ (e - (k + 1) * Nat.log p (A + B + k)) ∈ R := R.pow_mem (natCast_mem R p) _
  obtain ⟨h1, h2⟩ := H K k A B p R g hk hp hR f hf
  refine ⟨fun hG => ?_, fun hD => ?_⟩
  · rw [hpe, mul_smul]
    exact smul_mem_latOf_gauss R g hmem ((h1 hG).2 j hj)
  · rw [hpe, mul_smul]
    exact smul_mem_latOf_dual R g hmem ((h2 hD).2 j hj)
end Formalism.CountingSumsFrames.Har4
