-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count.dGT_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.657796+00:00
-- url     : https://prove2.me/submissions/ea534fdc-eaff-4097-8139-a50e11a0747e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
theorem _root_.solution (n : ℕ) : dGT n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : gtBox (0 : Fin (n + 1) → ℤ) = {0} := by
      ext κ
      simp [gtBox, Fintype.mem_piFinset, funext_iff]
    show ∑ κ ∈ gtBox (0 : Fin (n + 1) → ℤ), dGT n κ = 1
    rw [h, Finset.sum_singleton, ih]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
