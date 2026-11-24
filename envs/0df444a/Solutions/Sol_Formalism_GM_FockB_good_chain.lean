-- Prove2me | solution 1 for Formalism.GM.FockB.good_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:41.510986+00:00
-- url     : https://prove2.me/submissions/0278306a-1f3e-4aea-8f9a-46758f0e75d9

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_mulLeft_mem
import Theorems.Thm_Formalism_GM_FockB_good_of_ops
import Theorems.Thm_Formalism_GM_FockB_exists_op_eq_chainP
import Theorems.Thm_Formalism_GM_FockB_chainE_mem

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
variable {k σ α : Type} [Field k] {r : ℕ} (w e : α → Fin r → σ) (zv sv : α → σ) (z : α → ℕ)
variable {w e zv sv z}
namespace Formalism.GM.FockB
theorem _root_.solution (o n j : α → ℕ) (a : α) (L : List α) (hdisj : Disjoint (Va w e zv sv a) (VL w e zv sv L))
    {o0 n0 : ℕ} (Y0 : MvPolynomial σ k) (h : Good (w a) (e a) (zv a) (sv a) o0 n0 Y0) :
    Good (w a) (e a) (zv a) (sv a) o0 n0 (chainE w e zv sv j L * chainP w e zv sv z o n L Y0) := by
  obtain ⟨T, hT, hTe⟩ := exists_op_eq_chainP (k := k) (w := w) (e := e) (zv := zv) (sv := sv) (z := z) o n L
  have hHm := mulLeft_mem (chainE_mem (w := w) (e := e) (zv := zv) (sv := sv) (k := k) j L)
  rw [hTe]
  exact good_of_ops hdisj hHm (good_of_ops hdisj hT h)
end Formalism.GM.FockB
