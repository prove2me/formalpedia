-- Prove2me | solution 1 for Formalism.GM.ProjS.tv_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:11.11633+00:00
-- url     : https://prove2.me/submissions/0e39819a-d84b-4d14-8e98-169fd2708ae7

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
theorem _root_.solution (hv : M.TieVars w e zv sv) : Function.Injective (Fin.cons sv e : Fin (r + 1) → σ) := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact absurd hij.symm (hz j).2.2.2
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact absurd hij (hz i).2.2.2
    | succ j =>
      simp only [Fin.cons_succ] at hij
      rw [he hij]
end Formalism.GM.ProjS
