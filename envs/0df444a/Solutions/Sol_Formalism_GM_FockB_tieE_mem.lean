-- Prove2me | solution 1 for Formalism.GM.FockB.tieE_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:06.538823+00:00
-- url     : https://prove2.me/submissions/761484b2-e370-4e2d-9bb5-35422ae1a45a

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_mulLeft_mem
import Theorems.Thm_Formalism_GM_FockB_w_mem
import Theorems.Thm_Formalism_GM_FockB_e_mem
import Theorems.Thm_Formalism_GM_FockB_X_mem

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
theorem _root_.solution : (Formalism.GM.tieE w e : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) :=
  mulLeft_mem (sum_mem fun c _ => mul_mem (X_mem (w_mem c)) (X_mem (e_mem c)))
end Formalism.GM.FockB
