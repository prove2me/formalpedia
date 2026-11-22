-- Prove2me | solution 1 for Formalism.FG.InjVAux.HasOrd.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:37.201083+00:00
-- url     : https://prove2.me/submissions/d9e31099-5f42-4ff2-80c6-53971488040d

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open Formalism.FG.InjVAux
open MvPowerSeries
variable {R : Type*} [CommRing R] {τ : Type*}
namespace Formalism.FG.InjVAux
namespace HasOrd
theorem _root_.solution {m n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd m x) (hy : HasOrd n y) :
    HasOrd (m + n) (x * y) := by
  classical
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' : p.1 + p.2 = d := by simpa using hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by rw [← map_add, hp']
  by_cases h1 : p.1.degree < m
  · rw [hx _ h1, zero_mul]
  · rw [hy _ (by omega), mul_zero]
end HasOrd
end Formalism.FG.InjVAux
