-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.mv_map_invOfUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:44.081378+00:00
-- url     : https://prove2.me/submissions/0d716a67-9dad-45be-923c-66892699e2f4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries

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
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution {σ : Type*} (φ : R →+* S) (a : MvPowerSeries σ R) (e : Rˣ) (e' : Sˣ)
    (h : cc a = e) (h' : φ e = e') :
    MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)
      = MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by
  have h1 : a * MvPowerSeries.invOfUnit a e = 1 := MvPowerSeries.mul_invOfUnit a e h
  have h2 : MvPowerSeries.map φ a * MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by rw [MvPowerSeries.constantCoeff_map, h, h'])
  have h3 : MvPowerSeries.map φ a * MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e) = 1 := by
    rw [← map_mul, h1, map_one]
  calc MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)
      = MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e) *
          (MvPowerSeries.map φ a * MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e') := by
        rw [h2, mul_one]
    _ = (MvPowerSeries.map φ a * MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)) *
          MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by ring
    _ = MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by rw [h3, one_mul]
end Formalism.L2.Th1.A.Fgl1
