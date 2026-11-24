-- Prove2me | solution 1 for Formalism.GM.FockB.phi_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:57.757502+00:00
-- url     : https://prove2.me/submissions/ea5bf49d-779a-4ea1-9478-fce1860d3c7e

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm
import Theorems.Thm_Formalism_GM_FockB_mulLeft_mem
import Theorems.Thm_Formalism_GM_FockB_tiePhi_mem
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
    (o0 n0 z0 : ℕ) (Y0 : MvPolynomial σ k) :
    Formalism.GM.tiePhi (w a) (e a) o0 n0 z0 (chainE w e zv sv j L * chainP w e zv sv z o n L Y0) =
      chainE w e zv sv j L * chainP w e zv sv z o n L (Formalism.GM.tiePhi (w a) (e a) o0 n0 z0 Y0) := by
  obtain ⟨T, hT, hTe⟩ := exists_op_eq_chainP (k := k) (w := w) (e := e) (zv := zv) (sv := sv) (z := z) o n L
  have hHm := mulLeft_mem (chainE_mem (w := w) (e := e) (zv := zv) (sv := sv) (k := k) j L)
  have hPhi := tiePhi_mem (k := k) (w := w a) (e := e a) (zv := zv a) (sv := sv a) o0 n0 z0
  rw [hTe, hTe]
  have h1 := ops_apply_comm hdisj hPhi hHm (T Y0)
  have h2 := ops_apply_comm hdisj hPhi hT Y0
  simp only [LinearMap.mulLeft_apply] at h1
  rw [h1, h2]
end Formalism.GM.FockB
