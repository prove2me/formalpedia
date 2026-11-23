-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.map_invOfUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:42.259651+00:00
-- url     : https://prove2.me/submissions/9913f2cd-2007-49a9-b0c6-08d183df57a7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CurveSer
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
namespace Formalism.L2.Th1.A.CurveSer
theorem _root_.solution (φ : R →+* S) (a : R⟦X⟧) (e : Rˣ) (h : constantCoeff a = e) :
    PowerSeries.map φ (invOfUnit a e) = invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by
  have h1 : PowerSeries.map φ a * PowerSeries.map φ (invOfUnit a e) = 1 := by
    rw [← map_mul, PowerSeries.mul_invOfUnit a e h, map_one]
  have h2 : PowerSeries.map φ a * invOfUnit (PowerSeries.map φ a) (Units.map φ e) = 1 := by
    apply PowerSeries.mul_invOfUnit
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h]
    simp
  calc PowerSeries.map φ (invOfUnit a e)
      = PowerSeries.map φ (invOfUnit a e) *
          (PowerSeries.map φ a * invOfUnit (PowerSeries.map φ a) (Units.map φ e)) := by
        rw [h2, mul_one]
    _ = (PowerSeries.map φ a * PowerSeries.map φ (invOfUnit a e)) *
          invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by ring
    _ = invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by rw [h1, one_mul]
end Formalism.L2.Th1.A.CurveSer
