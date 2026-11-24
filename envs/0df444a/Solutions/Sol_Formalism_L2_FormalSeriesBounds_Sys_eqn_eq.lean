-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.eqn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:56.032129+00:00
-- url     : https://prove2.me/submissions/a9cb1fe3-0021-40e9-a92d-caaf3ac90b2d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_al_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {X : Cart V d I J}
open Formalism.L2.FormalSeriesBounds.Sys
variable (S : Sys X)
namespace Formalism.L2.FormalSeriesBounds.Sys
theorem _root_.solution (t : I → MvPowerSeries I C) (x : I) (μ : I →₀ ℕ) :
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ c : I,
        S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s))) =
      Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ := by
  rw [Finset.sum_range_succ', add_comm (Matrix.vecMul _ _ _)]
  congr 1
  all_goals first
    | rfl
    | (show _ = ∑ c, coeff μ (t c) * S.Mt c x
       exact Finset.sum_congr rfl fun c _ => by rw [S.al_zero c x, pow_zero, pow_one, mul_comm])
end Formalism.L2.FormalSeriesBounds.Sys
