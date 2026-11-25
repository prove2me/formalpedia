-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.a_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:25.070909+00:00
-- url     : https://prove2.me/submissions/5e88976b-d15a-46d3-b3bc-9c4298dacdd8

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution (i : Fin 5) : ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆] i ∈ Sadj W := by
  fin_cases i <;> exact Algebra.subset_adjoin (by simp)
end Formalism.ELL.CubeThreeAlt
