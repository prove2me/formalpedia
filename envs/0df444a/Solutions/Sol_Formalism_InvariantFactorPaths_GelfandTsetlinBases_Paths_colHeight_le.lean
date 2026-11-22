-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.colHeight_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:20.487015+00:00
-- url     : https://prove2.me/submissions/91412aa8-1097-496e-a1c0-e443a26d8195

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Paths
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
theorem _root_.solution {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : colHeight μ c ≤ n :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
