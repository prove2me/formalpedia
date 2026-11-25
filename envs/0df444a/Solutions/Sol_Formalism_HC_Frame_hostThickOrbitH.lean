-- Prove2me | solution 1 for Formalism.HC.Frame.hostThickOrbitH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:07:47.299519+00:00
-- url     : https://prove2.me/submissions/0df58734-30d8-44e4-a216-1549c7da0f9a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_addOrderOf_h_dvd
import Theorems.Thm_Formalism_HC_Frame_thick_part_one
import Theorems.Thm_Formalism_HC_Frame_thick_part_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
open Classical
namespace Formalism.HC.Frame
theorem _root_.solution {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (hR : NoRel T L)
    (u₀ t x : φ.A) :
    (4 * L < addOrderOf (φ.h x) → ∀ i₀ : ℤ,
      ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => φ.InTranslate T u₀ (t + i • x))).card ≤ 2) ∧
    (addOrderOf (φ.h x) ≤ 4 * L →
      {y : φ.A | (∃ i : ℤ, y = t + i • x) ∧ φ.InTranslate T u₀ y}.ncard ≤ 1) := by
  refine ⟨fun h i₀ => φ.thick_part_one T hT hR u₀ t x ?_ i₀, fun h => φ.thick_part_two T hT u₀ t x h⟩
  exact lt_of_lt_of_le h (Nat.le_of_dvd (addOrderOf_pos x) (φ.addOrderOf_h_dvd x))
end Formalism.HC.Frame
