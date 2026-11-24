-- Prove2me | solution 1 for Formalism.HC.EvenGrp.theta_toA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:15:45.428599+00:00
-- url     : https://prove2.me/submissions/daed2d46-6954-4b19-8154-b4cac21ff8a1

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_EvenData_xiA_toA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.EvenGrp
variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
variable (hev : ∀ χ ∈ Ξ, χ.Even)
namespace Formalism.HC.EvenGrp
theorem _root_.solution (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (s : G0) (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    theta Ξ e hev χ hχ (s, (data Ξ e hev).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) =
      χ.toUnitHom (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) := by
  show thetaB Ξ χ hχ ((data Ξ e hev).xiA ((data Ξ e hev).toA (ZMod.unitsMap (QS_dvd Ξ e) u))) = _
  have h1 : (data Ξ e hev).xiA ((data Ξ e hev).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) = xiW Ξ e u :=
    ((data Ξ e hev).xiA_toA (ZMod.unitsMap (QS_dvd Ξ e) u)).trans (xi_unitsMap Ξ e u)
  rw [h1]
  rfl
end Formalism.HC.EvenGrp
