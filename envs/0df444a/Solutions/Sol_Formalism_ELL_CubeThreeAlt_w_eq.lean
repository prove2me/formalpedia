-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.w_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:27.382899+00:00
-- url     : https://prove2.me/submissions/e049c9ba-08e4-4806-a780-7347107e8b82

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_low


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
variable {w : PowerSeries K}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution (hw : WFixed W w) : w = X ^ 3 * wU w := by
  obtain ⟨h0, h1, h2, -⟩ := Formalism.ELL.WeierstrassChordSeries.w_low hw
  ext n
  rw [PowerSeries.coeff_X_pow_mul', Formalism.ELL.wU]
  split_ifs with hn
  · rw [PowerSeries.coeff_mk, Nat.sub_add_cancel hn]
  · interval_cases n <;> assumption
end Formalism.ELL.CubeThreeAlt
