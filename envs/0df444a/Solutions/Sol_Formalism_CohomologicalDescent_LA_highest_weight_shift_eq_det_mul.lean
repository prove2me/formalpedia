-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.highest_weight_shift_eq_det_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:11.926374+00:00
-- url     : https://prove2.me/submissions/ddba7c3c-f710-4d61-94b4-518082641927

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_leading_minor_full_eq_det
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ} (ν : Fin r → ℕ) :
    hw R le_rfl (fun a => ν a + 1) = genericDet R r * hw R le_rfl ν := by
  cases r with
  | zero => simp [hw, genericDet]
  | succ r =>
    have hl : ∀ μ : Fin (r + 1) → ℕ, nuNext μ (Fin.last r) = 0 := fun μ => by simp [nuNext]
    have key : ∀ i : Fin r, ν i.castSucc + 1 - nuNext (fun a => ν a + 1) i.castSucc =
        ν i.castSucc - nuNext ν i.castSucc := by
      intro i
      have hs : (Fin.castSucc i).val + 1 < r + 1 := by
        have := i.isLt
        simp only [Fin.coe_castSucc]
        omega
      simp only [nuNext, dif_pos hs]
      omega
    have hL : ∀ (h1 : (Fin.last r).val + 1 ≤ r + 1) (h2 : (Fin.last r).val + 1 ≤ r + 1),
        lpMinor R ((Fin.last r).val + 1) h1 h2 = genericDet R (r + 1) :=
      fun h1 h2 => leading_minor_full_eq_det R _ (by simp) h1 h2
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [key, hl, Nat.sub_zero, hL]
    ring
end Formalism.CohomologicalDescent.LA
