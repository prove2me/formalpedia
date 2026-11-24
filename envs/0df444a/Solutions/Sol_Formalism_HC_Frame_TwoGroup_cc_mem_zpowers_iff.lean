-- Prove2me | solution 1 for Formalism.HC.Frame.TwoGroup.cc_mem_zpowers_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:38:36.487829+00:00
-- url     : https://prove2.me/submissions/16ce11cd-c233-4cf9-a43e-e441c56c9868

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_cc_mem_zpowers_iff
import Theorems.Thm_Formalism_HC_Frame_TwoGroup_orderOf_eq

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
variable {φ}
namespace Formalism.HC.Frame
namespace TwoGroup
theorem _root_.solution (h2 : φ.TwoGroup) (g : φ.GG) : φ.cc ∈ Subgroup.zpowers g ↔ g = φ.cc := by
  rw [φ.cc_mem_zpowers_iff]
  constructor
  · rintro ⟨hc, ho⟩
    obtain ⟨i, hi⟩ := h2.orderOf_eq g.2
    have h1 : orderOf g.2 = 1 := by
      rw [hi] at ho ⊢
      rcases i with _ | i
      · rfl
      · exact absurd ho (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero _⟩))
    exact Prod.ext hc (orderOf_eq_one_iff.1 h1)
  · rintro rfl
    exact ⟨rfl, by show Odd (orderOf (1 : φ.MA)); rw [orderOf_one]; exact odd_one⟩
end TwoGroup
end Formalism.HC.Frame
