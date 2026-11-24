-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.DD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:24.598797+00:00
-- url     : https://prove2.me/submissions/65e5abc4-2ba3-49b0-9671-ab59f30bc8ab

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {n : ℕ} (μ : ℕ → Fin n → ℤ) (N : ℕ) (m : Fin n) :
    DD μ N (N, m) = (|μ (N + 1) m - μ N m|).toNat := by
  unfold DD
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single m]
  · exact Finsupp.single_eq_same
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (Prod.mk.inj h).2
  · intro h
    exact absurd (Finset.mem_univ m) h
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
