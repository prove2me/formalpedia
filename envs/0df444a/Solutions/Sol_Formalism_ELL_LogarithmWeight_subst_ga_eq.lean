-- Prove2me | solution 1 for Formalism.ELL.LogarithmWeight.subst_ga_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:09.909268+00:00
-- url     : https://prove2.me/submissions/047c24bf-e83b-484c-ac81-239747ac1da1

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
import Theorems.Thm_Formalism_G_LogP_hs2


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
open Formalism Formalism.ELL Formalism.ELL.LogarithmWeight
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.LogarithmWeight
theorem _root_.solution {R : Type*} [CommRing R] (f : PowerSeries R) (hf0 : constantCoeff f = 0) :
    (FormalGroup.𝔾ₐ (R := R)).toPowerSeries.subst ![atX f, atY f] = atX f + atY f := by
  have hv := Formalism.G.LogP.hs2 (R := R) (u := atX f) (v := atY f)
    (PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0)
    (PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0)
  rw [FormalGroup.𝔾ₐ_toPowerSeries, MvPowerSeries.subst_add hv, MvPowerSeries.subst_X hv,
    MvPowerSeries.subst_X hv]
  rfl
end Formalism.ELL.LogarithmWeight
