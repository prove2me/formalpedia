-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.fcoord_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:58.366835+00:00
-- url     : https://prove2.me/submissions/983db269-83a1-4a96-a635-78c7a92566ba

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit

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
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x : V) : Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  unfold Formalism.HermitianLatticesTheory.fcoord
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
    first
      | (funext i; simp [Formalism.HermitianLatticesTheory.vecAt, map_mul])
      | (funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Finsupp.smul_apply, map_mul])
      | (unfold Formalism.HermitianLatticesTheory.vecAt; done)
  rw [hv, Matrix.mulVec_smul]
end Formalism.HN.PlaceDecomposition
