-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Contr.fixPt_close
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:35.060792+00:00
-- url     : https://prove2.me/submissions/ea9b3190-2251-46b6-bf81-45c6bd2b56e1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_coeff_iterate_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_iterate_zero


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
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {k : Type*} [Field k] {Z B : Type*}
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H
namespace Formalism.L2.FormalSeriesBounds.Contr
theorem _root_.solution (n : ℕ) (c : B) : OrdGE (n + 1) (H.fixPt c - Ψ^[n] 0 c) := by
  intro A hA
  rw [map_sub, ← H.coeff_iterate_zero c A (Nat.lt_succ_iff.mp hA), sub_self]
end Formalism.L2.FormalSeriesBounds.Contr
