-- Prove2me | solution 1 for Formalism.UnitaryBoundIntegral.ubint_mvExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:39:56.960419+00:00
-- url     : https://prove2.me/submissions/3e546e84-3d36-4450-89a5-5e4f24c112a3

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Definitions.Def_Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero

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
open MvPowerSeries Finset
open Formalism Formalism.UnitaryBoundIntegral
open Formalism.IncomingBounds
variable {C : Type} [Field C] {σ : Type}
namespace Formalism.UnitaryBoundIntegral
theorem _root_.solution : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  change ∑ k ∈ Finset.range (m.degree + 1), coeff m ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C) =
    coeff m 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    simp at h
end Formalism.UnitaryBoundIntegral
