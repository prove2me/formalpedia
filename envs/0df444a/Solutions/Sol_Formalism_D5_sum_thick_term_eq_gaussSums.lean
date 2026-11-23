-- Prove2me | solution 1 for Formalism.D5.sum_thick_term_eq_gaussSums
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:13.074801+00:00
-- url     : https://prove2.me/submissions/b7f03a25-abc7-4334-b85d-b25cb505934e

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Theorems.Thm_Formalism_D5_phiSet_card
import Theorems.Thm_Formalism_D5_sum_H
import Theorems.Thm_Formalism_D5_sum_trivH
import Theorems.Thm_Formalism_D5_sum_character_shift_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
open Classical
namespace Formalism.D5
theorem _root_.solution {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (t : H) (j : Fin m) :
    ∑ u0 : H, thickZ Hs Nd u0 t j = ((Nd.T2.card : ℂ) / 2) * ((Nd.bj j : ℝ) : ℂ) *
      (GC Hs 0 (Nd.a t / Nd.bj j) + GC Hs Hs.psC (Nd.a t / Nd.bj j) - GC Hs Hs.chC (Nd.a t / Nd.bj j)
        - GC Hs Hs.chpsC (Nd.a t / Nd.bj j)) := by
  unfold thickZ
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hin : ∀ s ∈ Nd.T2, ∑ u0 : H, ∑ ψ : AddChar (E0 × H) ℂ,
      ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) * ((Nd.bj j : ℝ) : ℂ)
        * GC Hs ψ (Nd.a t / Nd.bj j)
      = (Fintype.card H : ℂ) * ((Nd.bj j : ℝ) : ℂ) * ∑ ψ : AddChar (E0 × H) ℂ,
          (if TrivH ψ then ψ e10 * GC Hs ψ (Nd.a t / Nd.bj j) else 0) := by
    intro s _
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_character_shift_eq, sum_H]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul, sum_trivH, phiSet_card]
  have hH : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  push_cast
  field_simp
end Formalism.D5
