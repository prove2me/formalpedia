-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.fcoord_lincomb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:07:00.266463+00:00
-- url     : https://prove2.me/submissions/5a650a86-9b85-457c-b599-d2aab19cb7e9

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_fcoord_smul

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    {n : Type*} [Fintype n] (c : n → K) (y : n → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ k, c k • y k) = ∑ k, v.embedding (c k) • Formalism.HermitianLatticesTheory.fcoord b X v (y k) := by
  have hadd : ∀ x y : V, Formalism.HermitianLatticesTheory.fcoord b X v (x + y) =
      Formalism.HermitianLatticesTheory.fcoord b X v x + Formalism.HermitianLatticesTheory.fcoord b X v y := by
    intro x y
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have hzero : Formalism.HermitianLatticesTheory.fcoord b X v 0 = 0 := by
    simpa using fcoord_smul b X v 0 0
  let F : V →+ (ι → ℂ) :=
    { toFun := Formalism.HermitianLatticesTheory.fcoord b X v, map_zero' := hzero, map_add' := hadd }
  change F (∑ k, c k • y k) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => fcoord_smul b X v (c k) (y k)
end Formalism.HN.PlaceDecomposition
