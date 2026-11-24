-- Prove2me | solution 1 for Formalism.IndefR.Eqv.snoc_eq_cons_rot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:27.751126+00:00
-- url     : https://prove2.me/submissions/c4362bd8-35bb-4909-b90f-63fd1ec0b8bb

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace Formalism.IndefR.Eqv
theorem _root_.solution {n : ℕ} (w : V) (vs : Fin n → V) :
    (Fin.snoc vs w : Fin (n + 1) → V) = (Fin.cons w vs : Fin (n + 1) → V) ∘ finRotate (n + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [finRotate_last]
  · simp only [Fin.snoc_castSucc, Function.comp_apply]
    rw [finRotate_succ_apply, Fin.coeSucc_eq_succ, Fin.cons_succ]
end Formalism.IndefR.Eqv
