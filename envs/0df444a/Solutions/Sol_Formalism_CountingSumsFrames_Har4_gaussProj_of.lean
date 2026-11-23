-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.gaussProj_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:05.687632+00:00
-- url     : https://prove2.me/submissions/8a1bd5f3-4471-4420-b867-c222327372d2

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_harProj_mem_PolAB
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_levelProj_mem_PolAB
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_gauss_dual_of_fock

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
theorem _root_.solution (H : FockProj) : GaussProj := by
  intro K _ _ k A B p R g hk hp hR f hf
  have hhar := gauss_dual_of_fock R g hk hp hR (harProj K k A B) (fun f' hf' => harProj_mem_PolAB hf')
    (Nat.log p (A + B + k)) (by omega) (fun f' hf' hfl => (H K k A B p R g hk hp hR f' hf' hfl).1) f hf
  have lev := fun (j : ℕ) (hj : j ≤ min A B) => gauss_dual_of_fock R g hk hp hR (levelProj K k A B j)
    (fun f' hf' => levelProj_mem_PolAB hj hf') (2 * Nat.log p (A + B + k)) le_rfl
    (fun f' hf' hfl => (H K k A B p R g hk hp hR f' hf' hfl).2 j hj) f hf
  exact ⟨fun hG => ⟨hhar.1 hG, fun j hj => (lev j hj).1 hG⟩,
    fun hD => ⟨hhar.2 hD, fun j hj => (lev j hj).2 hD⟩⟩
end Formalism.CountingSumsFrames.Har4
