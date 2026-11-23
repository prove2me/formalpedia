-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.intercept_mem_integralSeries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:47.151819+00:00
-- url     : https://prove2.me/submissions/443f1e45-d2ad-43f5-a565-41f9d7dc1262

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_X_mem_T
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_slope_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_wVar_mem_integralSeries

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
theorem _root_.solution (hw : WFixed W w) : nu w ∈ T W := by
  exact sub_mem (wVar_mem_integralSeries hw 0) (mul_mem (slope_mem_integralSeries hw) (X_mem_T 0))
end Formalism.ELL.WeierstrassChordSeries
