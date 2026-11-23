-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:25.944241+00:00
-- url     : https://prove2.me/submissions/401d7c95-22ba-4601-9d84-2edf918b2a8f

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_mul
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constantCoeff_thirdParam
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_linearCoeff_thirdParam
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_dd_cc

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
theorem _root_.solution (hw : WFixed W w) (i : Fin 2) : (L i) (F2 W w) = 1 := by
  rw [F2, L_mul, constantCoeff_thirdParam hw, linearCoeff_thirdParam hw,
    MvPowerSeries.constantCoeff_inv, dd_cc hw]
  norm_num
end Formalism.ELL.WeierstrassChordSeries
