-- Prove2me | solution 1 for Formalism.GM.ProjS.tieFh_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:13.073769+00:00
-- url     : https://prove2.me/submissions/dc0aaa43-4fc6-4bd8-b812-2ca3be3a16db

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS

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
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    (M.tieFh w e zv sv : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) =
      tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) := by
  unfold Formalism.GM.M.tieFh Formalism.GM.tieF
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
end Formalism.GM.ProjS
