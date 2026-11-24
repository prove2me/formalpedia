-- Prove2me | solution 1 for Formalism.HC.EvenData.twoGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:53:35.336088+00:00
-- url     : https://prove2.me/submissions/a33fb147-a3a1-4d8b-9a2d-a3b317ef2dde

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Theorems.Thm_Formalism_HC_EvenData_ord_eq
import Theorems.Thm_Formalism_HC_D7_ord_eq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_towerProperties


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
attribute [instance] EvenData.grp
open Formalism.HC.EvenData
variable (D : EvenData)
namespace Formalism.HC.EvenData
theorem _root_.solution (h : ∃ j : ℕ, ∀ u, D.ξ u ^ 2 ^ j = 1) : D.frame.TwoGroup := by
  obtain ⟨j, hj⟩ := h
  have hcard : Nat.card (HGrp D.e) = 2 ^ D.e := (Formalism.TwoAdicCyclotomicDecomposition.towerProperties.1.2.1 D.e).2.1
  have hpg : IsPGroup 2 D.R := by
    rintro ⟨_, u, rfl⟩
    refine ⟨D.e + j, ?_⟩
    apply Subtype.ext
    show D.eta u ^ 2 ^ (D.e + j) = 1
    refine Prod.ext ?_ ?_
    · show D.cl u ^ 2 ^ (D.e + j) = 1
      rw [show (2 : ℕ) ^ (D.e + j) = 2 ^ D.e * 2 ^ j from pow_add 2 D.e j, pow_mul, ← hcard,
        pow_card_eq_one', one_pow]
    · show D.ξ u ^ 2 ^ (D.e + j) = 1
      rw [show (2 : ℕ) ^ (D.e + j) = 2 ^ j * 2 ^ D.e by rw [pow_add, mul_comm], pow_mul, hj, one_pow]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  exact ⟨n, (D.ord_eq).trans hn⟩
end Formalism.HC.EvenData
