-- Prove2me | solution 1 for Formalism.GM.FockB.pderiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:02.398636+00:00
-- url     : https://prove2.me/submissions/57e16b5c-76af-4d3e-be7f-f1d850935dff

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
theorem _root_.solution {S : Set σ} {u : σ} (hu : u ∈ S) :
    ((pderiv u : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)).toLinearMap) ∈ Ops S :=
  Algebra.subset_adjoin ⟨u, hu, Or.inr rfl⟩
end Formalism.GM.FockB
