-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.coeff_logSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:40.948639+00:00
-- url     : https://prove2.me/submissions/07cbcf3c-f991-4c1d-8748-dc3c81326a3f

import Definitions.Def_Formalism_FrobeniusBaseCase_StatementFix
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (t : C → MvPowerSeries Z k) (b : C) (A : Z →₀ ℕ) (N : ℕ) :
    coeff A (∑ c, ∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j)) =
      ∑ c, ∑ j ∈ Finset.Icc 1 N, D.al c j b * coeff A (t c ^ (D.l ^ j)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => coeff_C_mul _ _ _
end Formalism.BaseCaseIdentities.Data
