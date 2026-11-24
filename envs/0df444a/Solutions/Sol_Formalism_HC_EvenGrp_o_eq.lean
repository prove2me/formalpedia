-- Prove2me | solution 1 for Formalism.HC.EvenGrp.o_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:47:16.820236+00:00
-- url     : https://prove2.me/submissions/d9069fdc-fed0-4309-bc9d-bd35fa7780c1

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_EvenGrp_card_B
import Theorems.Thm_Formalism_HC_EvenGrp_xi_surj
import Theorems.Thm_Formalism_HC_EvenData_exact
import Theorems.Thm_Formalism_HC_EvenData_o_eq


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
theorem _root_.solution : (frame Ξ e hev).o = Nat.card Ξ := by
  rw [← card_B Ξ]
  refine ((data Ξ e hev).o_eq).trans ?_
  show Nat.card (xi Ξ e).range = Nat.card (B Ξ)
  rw [MonoidHom.range_eq_top.mpr (xi_surj Ξ e)]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv
end Formalism.HC.EvenGrp
