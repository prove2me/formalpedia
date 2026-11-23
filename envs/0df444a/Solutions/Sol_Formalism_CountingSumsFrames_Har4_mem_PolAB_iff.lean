-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.mem_PolAB_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:33.414997+00:00
-- url     : https://prove2.me/submissions/cf376642-9cb4-4b2f-b0c9-ceb2f3ba8c3f

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_weight_wXY

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
theorem _root_.solution {K : Type} [Field K] {k A B : ℕ} (f : PolXY K k) :
    f ∈ PolAB K k A B ↔ IsWeightedHomogeneous (wXY k) f (A, B) := by
  constructor
  · intro hf d hd
    have hf' : ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B := hf
    have h1 := hf' d (MvPolynomial.mem_support_iff.2 hd)
    rw [weight_wXY, h1.1, h1.2]
  · intro hf
    show ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B
    intro m hm
    have h1 := hf (MvPolynomial.mem_support_iff.1 hm)
    rw [weight_wXY] at h1
    exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
end Formalism.CountingSumsFrames.Har4
