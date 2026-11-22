-- Prove2me | solution 1 for Formalism.GM.ProjS.tieP_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:55.718854+00:00
-- url     : https://prove2.me/submissions/cd3c15e2-f672-4b08-84be-c6df53d9e198

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_tieEh_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution (o n z : ℕ) (y : MvPolynomial σ k) :
    M.tieP w e zv sv o n z y = ∑ l ∈ range (o + 1),
      (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) •
        (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l) ((tieF w e ^ l) (X zv ^ z * y)) := by
  unfold Formalism.GM.M.tieP
  rw [tieEh_eq]
end Formalism.GM.ProjS
