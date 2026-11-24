-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.finrank_real_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:22.192843+00:00
-- url     : https://prove2.me/submissions/9896ad03-08be-4beb-9ebd-af851b05d79f

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_span_real_eq_complex
import Theorems.Thm_Formalism_HN_PlaceDecomposition_finrank_span_complex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    finrank ℝ (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))) = 2 * rkK N := by
  rw [← span_real_eq_complex b X N v, ← finrank_span_complex b X hX N v]
  exact finrank_real_of_complex _
end Formalism.HN.PlaceDecomposition
