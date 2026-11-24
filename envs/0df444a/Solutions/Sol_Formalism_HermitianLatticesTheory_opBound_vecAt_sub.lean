-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.opBound_vecAt_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:01.514914+00:00
-- url     : https://prove2.me/submissions/24b317c1-ff0e-440c-86d8-16a1bfa7ae76

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (b : Module.Basis ι K V) (v : InfinitePlace K) (x y : V) :
    vecAt b v (x - y) = vecAt b v x - vecAt b v y := by
  funext i; simp [vecAt, map_sub]
end Formalism.HermitianLatticesTheory
