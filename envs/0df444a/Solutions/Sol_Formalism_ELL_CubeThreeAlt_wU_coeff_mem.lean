-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.wU_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:14.14181+00:00
-- url     : https://prove2.me/submissions/14137c62-e876-4e6f-862d-9a861d0dadb0

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_coeff_mem


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
theorem _root_.solution (hw : WFixed W w) (n : ℕ) : coeff n (wU w) ∈ Sadj W := by
  rw [Formalism.ELL.wU, PowerSeries.coeff_mk]
  exact Formalism.ELL.WeierstrassChordSeries.w_coeff_mem hw _
end Formalism.ELL.CubeThreeAlt
