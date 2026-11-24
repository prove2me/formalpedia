-- Prove2me | solution 1 for Formalism.CohomologicalDescent.labelSumLe_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:15:22.857293+00:00
-- url     : https://prove2.me/submissions/eaf15755-377b-4de7-81d0-10dfaae729c7

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Theorems.Thm_Formalism_CohomologicalDescent_label_sum_le_filter
import Theorems.Thm_Formalism_CohomologicalDescent_label_card_le
import Theorems.Thm_Formalism_CohomologicalDescent_label_second

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution : LabelSum := by
  intro l k t h i xm xp mB hl hi hmB hmx hxx hxh hh hlh
  unfold labelLHS labelSumBound
  have hlpos : 0 < l := hl.pos
  have hhZ : (h : ℤ) < (l : ℤ) ^ 2 := by exact_mod_cast hh
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hA := label_sum_le_filter hl (Finset.Icc xm xp) mB (fun _ => (k : ℝ))
    (fun _ _ => hk) (fun x hx => by
      rw [Finset.mem_Icc] at hx
      exact ⟨by omega, by linarith [hx.2]⟩)
  rw [Finset.sum_const, nsmul_eq_mul] at hA
  have hB : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ) ≤
      ((xp - xm : ℤ) : ℝ) / l + IlInd l xm xp mB := by
    unfold IlInd
    split_ifs with hex
    · exact label_card_le hlpos xm xp mB hxx
    · have hempty : (Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx hd
        rw [Finset.mem_Icc] at hx
        exact hex ⟨x, hx.1, hx.2, hd⟩
      rw [hempty, Finset.card_empty, Nat.cast_zero, add_zero]
      apply div_nonneg
      · exact_mod_cast (by omega : (0 : ℤ) ≤ xp - xm)
      · exact Nat.cast_nonneg _
  have hC := label_second (k := k) (t := t) hl hi hmB hmx (by omega) hh hlh
  have hkB := mul_le_mul_of_nonneg_left hB hk
  linarith
end Formalism.CohomologicalDescent
