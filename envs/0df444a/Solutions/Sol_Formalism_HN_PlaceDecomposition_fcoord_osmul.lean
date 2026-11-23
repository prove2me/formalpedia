-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.fcoord_osmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:55.929813+00:00
-- url     : https://prove2.me/submissions/df44d7af-1b69-46bc-92e1-a4653d8aaba3

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
    (a : 𝓞 K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding (a : K) • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  rw [← algebraMap_smul K a x]
  exact fcoord_smul b X v _ x
end Formalism.HN.PlaceDecomposition
