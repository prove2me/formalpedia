-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.coeff_Ps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:44.957805+00:00
-- url     : https://prove2.me/submissions/f263b00c-81d8-4233-b20b-2836e7bc8908

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
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
theorem _root_.solution (t : I → MvPowerSeries I C) (c : I) (μ : I →₀ ℕ) :
    coeff μ (S.Ps t c) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹ c := rfl
end Formalism.L2.FormalSeriesBounds.Sys
