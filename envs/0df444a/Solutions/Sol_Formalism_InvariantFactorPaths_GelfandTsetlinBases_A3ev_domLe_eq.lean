-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.domLe_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:49.531423+00:00
-- url     : https://prove2.me/submissions/7272ad39-5b96-4350-b419-5e211a27d4d1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_eq_of_psum

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
theorem _root_.solution {n : ℕ} {μ ν : Fin n → ℤ} (h : DomLe μ ν) (hh : height ν ≤ height μ) : ν = μ := by
  have hle : ∀ j, psum μ j ≤ psum ν j := h.2
  have heq : ∀ j ∈ range (n + 1), psum μ j = psum ν j :=
    (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).1
      (le_antisymm (Finset.sum_le_sum fun j _ => hle j) hh)
  exact eq_of_psum fun j hj => (heq j (Finset.mem_range.2 (by omega))).symm
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
