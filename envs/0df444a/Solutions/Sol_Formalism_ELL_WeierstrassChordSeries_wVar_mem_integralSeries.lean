-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.wVar_mem_integralSeries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:51.374054+00:00
-- url     : https://prove2.me/submissions/3c94390a-43f6-44c1-a5d6-bdf97bf46278

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_coeff_mem
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_Wi
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_mem_T

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
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (hw : WFixed W w) (i : Fin 2) : Wi w i ∈ T W := by
  rw [mem_T]
  intro e
  rw [coeff_Wi]
  split_ifs
  · exact w_coeff_mem hw _
  · exact zero_mem _
end Formalism.ELL.WeierstrassChordSeries
