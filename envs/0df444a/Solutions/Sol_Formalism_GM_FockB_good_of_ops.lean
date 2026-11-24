-- Prove2me | solution 1 for Formalism.GM.FockB.good_of_ops
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:56.442364+00:00
-- url     : https://prove2.me/submissions/4951d062-0354-481f-9c4c-78828024e07b

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem
import Theorems.Thm_Formalism_GM_FockB_w_mem
import Theorems.Thm_Formalism_GM_FockB_e_mem
import Theorems.Thm_Formalism_GM_FockB_zv_mem
import Theorems.Thm_Formalism_GM_FockB_sv_mem
import Theorems.Thm_Formalism_GM_FockB_eulL_mem

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
theorem _root_.solution {S : Set σ} (hS : Disjoint (V w e zv sv) S) {T : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ Ops S) {o n : ℕ} {y : MvPolynomial σ k} (hy : Good w e zv sv o n y) :
    Good w e zv sv o n (T y) := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ops_apply_comm hS (eulL_mem w (fun c => w_mem c)) hT, h1, map_smul]
  · rw [ops_apply_comm hS (eulL_mem e (fun c => e_mem c)) hT, h2, map_smul]
  · have := ops_apply_comm hS (pderiv_mem (k := k) (zv_mem (w := w) (e := e) (sv := sv))) hT y
    simp only [Derivation.coeFn_coe] at this
    rw [this, h3, map_zero]
  · have := ops_apply_comm hS (pderiv_mem (k := k) (sv_mem (w := w) (e := e) (zv := zv))) hT y
    simp only [Derivation.coeFn_coe] at this
    rw [this, h4, map_zero]
end Formalism.GM.FockB
