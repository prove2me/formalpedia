-- Prove2me | solution 1 for Formalism.GM.FockB.X_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:12.779151+00:00
-- url     : https://prove2.me/submissions/defdc35e-4d51-429b-ae7f-c503df9ab3e8

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
variable {k σ : Type} [Field k] {r : ℕ}
variable {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.FockB
theorem _root_.solution {S : Set σ} {u : σ} (hu : u ∈ S) : (X u : MvPolynomial σ k) ∈ Algebra.adjoin k (X '' S) :=
  Algebra.subset_adjoin ⟨u, hu, rfl⟩
end Formalism.GM.FockB
