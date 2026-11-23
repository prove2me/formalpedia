-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.prj_realize
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:38.457479+00:00
-- url     : https://prove2.me/submissions/d318f1db-c124-4e0d-b0d5-450f0a94633a

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_realize_apply
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_apply
import Theorems.Thm_Formalism_HN_PlaceDecomposition_psi_apply

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
variable [DecidableEq (InfinitePlace K)]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : prj v (Formalism.HermitianLatticesTheory.realize b X x) = psi v (Formalism.HermitianLatticesTheory.fcoord b X v x) := by
  ext p
  rw [prj_apply, psi_apply, realize_apply]
  split_ifs with h1 h2 <;> (try subst h1) <;> rfl
end Formalism.HN.PlaceDecomposition
