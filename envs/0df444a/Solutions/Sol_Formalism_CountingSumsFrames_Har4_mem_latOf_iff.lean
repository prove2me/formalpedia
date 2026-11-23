-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.mem_latOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:33.161124+00:00
-- url     : https://prove2.me/submissions/221d1c59-616a-4fdb-a818-03d2121daca4

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_inv_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_glAct_inv

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
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (S : Set (PolXY K k)) (f : PolXY K k) :
    f ∈ latOf g S ↔ glAct g⁻¹ f ∈ S := by
  constructor
  · rintro ⟨h, hS, rfl⟩
    rwa [glAct_inv_glAct]
  · intro hf
    exact ⟨glAct g⁻¹ f, hf, glAct_glAct_inv g f⟩
end Formalism.CountingSumsFrames.Har4
