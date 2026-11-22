-- Prove2me | solution 1 for Formalism.GM.ProjS.tv_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:59.481655+00:00
-- url     : https://prove2.me/submissions/982a0755-2c01-4a46-8ef6-fabe77bef35a

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
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution (hv : M.TieVars w e zv sv) : Function.Injective (Fin.cons zv w : Fin (r + 1) → σ) := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact absurd hij.symm (hz j).1
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact absurd hij (hz i).1
    | succ j =>
      simp only [Fin.cons_succ] at hij
      rw [hw hij]
end Formalism.GM.ProjS
