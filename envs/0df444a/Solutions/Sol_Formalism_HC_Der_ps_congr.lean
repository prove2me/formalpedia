-- Prove2me | solution 1 for Formalism.HC.Der.ps_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:04:09.909877+00:00
-- url     : https://prove2.me/submissions/4b28006d-8788-4b16-b0fd-c75b33a5feb6

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_val_modEq_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution (u w : (ZMod H.condN)ˣ) (h : ZMod.unitsMap (QSq_dvd H) u = ZMod.unitsMap (QSq_dvd H) w) :
    (H.art u).1.1 = (H.art w).1.1 := by
  haveI : NeZero H.condN := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos)⟩
  have h1 : ZMod.unitsMap (QSq_dvd H) (u * w⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := H.art_d (u * w⁻¹) ((val_modEq_one_iff (QSq_dvd H) _).mpr h1)
  have h3 : (H.art (u * w⁻¹)).1.1 = 1 := by
    rcases h2 with h2 | h2 <;> rw [h2] <;> rfl
  have h4 : H.art u = H.art (u * w⁻¹) * H.art w := by rw [← map_mul, inv_mul_cancel_right]
  rw [h4, Prod.fst_mul, Prod.fst_mul, h3, one_mul]
end Formalism.HC.Der
