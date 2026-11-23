-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.Wi_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:20.706311+00:00
-- url     : https://prove2.me/submissions/2e67b4c1-4c36-4440-a6b8-eab61dd9305c

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_low
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_Wi

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
theorem _root_.solution (hw : WFixed W w) (i j : Fin 2) : (L j) (Wi w i) = 0 := by
  rw [coeff_Wi]
  by_cases h : j = i
  · subst h
    simp [(w_low hw).2.1]
  · simp [Finsupp.single_apply, h, (w_low hw).1, hw.1]
end Formalism.ELL.WeierstrassChordSeries
