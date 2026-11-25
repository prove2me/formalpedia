-- Prove2me | solution 1 for Formalism.HC.Frame.hostThickOrbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:05:23.19798+00:00
-- url     : https://prove2.me/submissions/058fa62a-7838-4f8f-90a9-de42d6ace0cc

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
    (4 * L < addOrderOf x → ∀ i₀ : ℤ,
      ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => φ.InTranslate T u₀ (t + i • x))).card ≤ 2) ∧
    (addOrderOf x ≤ 4 * L →
      {y : φ.A | (∃ i : ℤ, y = t + i • x) ∧ φ.InTranslate T u₀ y}.ncard ≤ 1) := by
  refine ⟨fun h i₀ => φ.thick_part_one T hT hR u₀ t x h i₀, fun h => φ.thick_part_two T hT u₀ t x ?_⟩
  exact le_trans (Nat.le_of_dvd (addOrderOf_pos x) (φ.addOrderOf_h_dvd x)) h
end Formalism.HC.Frame
