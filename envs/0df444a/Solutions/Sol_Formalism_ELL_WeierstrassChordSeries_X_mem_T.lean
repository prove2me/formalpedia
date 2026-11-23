-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.X_mem_T
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:16.8859+00:00
-- url     : https://prove2.me/submissions/6083ff0e-2fd9-40e8-8371-174bc5180071

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
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
theorem _root_.solution (i : Fin 2) : (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ∈ T W := by
  rw [mem_T]
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _
end Formalism.ELL.WeierstrassChordSeries
