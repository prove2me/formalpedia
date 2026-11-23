-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_pderiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:51.466017+00:00
-- url     : https://prove2.me/submissions/b38b3ad1-3aac-415a-ba19-4d064dad8aab

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_pderiv_comm
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_pderiv_X_inj


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
theorem _root_.solution {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (c0 : Fin s)
    (h : MvPolynomial σ k) :
    eulL t (pderiv (t c0) h) = pderiv (t c0) (eulL t h) - pderiv (t c0) h := by
  have key : pderiv (t c0) (eulL t h) = pderiv (t c0) h + eulL t (pderiv (t c0) h) := by
    rw [eulL_apply, eulL_apply, map_sum]
    have hc : ∀ c, pderiv (t c0) (X (t c) * pderiv (t c) h) =
        (if c = c0 then pderiv (t c) h else 0) + X (t c) * pderiv (t c) (pderiv (t c0) h) := by
      intro c
      rw [MvPolynomial.pderiv_mul, Formalism.GM.pderiv_X_inj ht, pderiv_comm (t c0) (t c)]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun c _ => hc c), Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
  rw [key]
  ring
end Formalism.GM.ProjS
