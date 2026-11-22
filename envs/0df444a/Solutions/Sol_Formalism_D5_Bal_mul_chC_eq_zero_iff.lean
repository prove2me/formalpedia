-- Prove2me | solution 1 for Formalism.D5.Bal.mul_chC_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:21.723827+00:00
-- url     : https://prove2.me/submissions/873e698c-9bf0-4705-ba48-22bc2864e220

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Theorems.Thm_Formalism_D5_Bal_chC_mul_self
import Theorems.Thm_Formalism_D5_Bal_chC_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5.Bal
theorem _root_.solution (Hs : CycHost H) (ψ : AddChar (E0 × H) ℂ) : ψ * Hs.chC = 0 ↔ ψ = Hs.chC := by
  constructor
  · intro h
    refine AddChar.ext _ _ (fun g => ?_)
    have h1 : ψ g * Hs.chC g = 1 := by
      rw [← AddChar.mul_apply, h, AddChar.zero_apply]
    calc ψ g = ψ g * (Hs.chC g * Hs.chC g) := by rw [chC_sq, mul_one]
      _ = (ψ g * Hs.chC g) * Hs.chC g := by ring
      _ = Hs.chC g := by rw [h1, one_mul]
  · rintro rfl
    exact chC_mul_self Hs
end Formalism.D5.Bal
