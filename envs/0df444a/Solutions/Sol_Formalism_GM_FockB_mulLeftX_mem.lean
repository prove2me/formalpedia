-- Prove2me | solution 1 for Formalism.GM.FockB.mulLeftX_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:25.476276+00:00
-- url     : https://prove2.me/submissions/c441a9ae-7745-483e-9d08-9baf3e38f02e

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.FockB
theorem _root_.solution {S : Set σ} {u : σ} (hu : u ∈ S) : LinearMap.mulLeft k (X u : MvPolynomial σ k) ∈ Ops S :=
  Algebra.subset_adjoin ⟨u, hu, Or.inl rfl⟩
end Formalism.GM.FockB
