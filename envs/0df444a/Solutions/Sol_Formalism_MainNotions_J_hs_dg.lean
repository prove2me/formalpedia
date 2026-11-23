-- Prove2me | solution 1 for Formalism.MainNotions.J.hs_dg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:38.371896+00:00
-- url     : https://prove2.me/submissions/920ea154-7bd9-4160-98cf-9fef880b0673

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
import Theorems.Thm_Formalism_MainNotions_J_cc_dg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]
namespace Formalism.MainNotions.J
theorem _root_.solution {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) :
    HasSubst (diagS a : ι → MvPowerSeries ι R) where
  const_coeff s := by rw [cc_dg ha]; exact IsNilpotent.zero
  coeff_zero d := by
    classical
    refine (d.support.finite_toSet).subset ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    unfold diagS at hs
    rw [PowerSeries.coeff_subst_single] at hs
    by_contra hns
    have h0 : d s = 0 := by simpa using hns
    split_ifs at hs with h1
    · rw [h0] at hs
      exact hs (by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ha])
    · exact hs rfl
end Formalism.MainNotions.J
