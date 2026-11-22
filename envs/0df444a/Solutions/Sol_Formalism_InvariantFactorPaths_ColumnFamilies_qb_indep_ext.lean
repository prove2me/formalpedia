-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_indep_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:23.779981+00:00
-- url     : https://prove2.me/submissions/94df846d-fda0-4826-91a2-afaecc06bd69

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {k W κ ι : Type*} [Field k] [AddCommGroup W] [Module k W] [Fintype κ] (c : κ → ι → k)
    (hc : LinearIndependent k c) (f : κ → W) (h : ∀ i, ∑ j, c j i • f j = 0) : ∀ j, f j = 0 := by
  intro j
  by_contra hne
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual k W, l (f j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Module.forall_dual_apply_eq_zero_iff k (f j)).1 hcon)
  refine hl (Fintype.linearIndependent_iff.1 hc (fun j => l (f j)) ?_ j)
  funext i
  have := congrArg l (h i)
  simpa [map_sum, mul_comm] using this
end Formalism.InvariantFactorPaths.ColumnFamilies
