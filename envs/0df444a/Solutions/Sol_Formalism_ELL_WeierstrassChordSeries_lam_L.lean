-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.lam_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:36.430333+00:00
-- url     : https://prove2.me/submissions/f45160e6-98c9-41e8-949b-a72443329ce7

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_low
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_lam

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
theorem _root_.solution (hw : WFixed W w) (i : Fin 2) : (L i) (lam w) = 0 := by
  have h : (Finsupp.single i 1) 0 + (Finsupp.single i 1) 1 = 1 := by
    fin_cases i <;> simp
  rw [coeff_lam, h]
  exact (w_low hw).2.2.1
end Formalism.ELL.WeierstrassChordSeries
