-- Prove2me | solution 1 for Formalism.GM.ProjS.tieEh_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:54.670019+00:00
-- url     : https://prove2.me/submissions/6eac479a-cc1e-4c20-b1e9-02892d8fafa3

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
    (M.tieEh w e zv sv : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) =
      tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) := by
  unfold Formalism.GM.M.tieEh Formalism.GM.tieE
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
end Formalism.GM.ProjS
