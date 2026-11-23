-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.nu_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:14.259316+00:00
-- url     : https://prove2.me/submissions/e1b57544-6543-476e-baee-1b5383aa2b22

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_mul
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_Wi_L
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_L

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
theorem _root_.solution (hw : WFixed W w) (i : Fin 2) : (L i) (nu w) = 0 := by
  rw [nu, map_sub, L_mul, Wi_L hw, lam_cc hw, lam_L hw]
  simp
end Formalism.ELL.WeierstrassChordSeries
