-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.JmuHC.prod_one_add_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:41.369623+00:00
-- url     : https://prove2.me/submissions/35ceacdd-82f3-472f-b21e-8b3094d6d20b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJmuHC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.JmuHC
open Finset
namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC
theorem _root_.solution (D : Finset ℕ) (h0 : 0 ∉ D) : ∏ d ∈ D, (1 + 1 / (d : ℝ)) ≤ D.card + 1 := by
  induction D using Finset.induction_on_max with
  | empty => simp
  | insert m D hlt ih =>
    have hm : m ∉ D := fun h => lt_irrefl _ (hlt m h)
    have h0' : 0 ∉ D := fun h => h0 (mem_insert_of_mem h)
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun e => h0 (e ▸ mem_insert_self m D)
    have hcard : D.card + 1 ≤ m := by
      have hsub : D ⊆ (range m).erase 0 := fun x hx =>
        mem_erase.2 ⟨fun e => h0' (e ▸ hx), mem_range.2 (hlt x hx)⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (mem_range.2 hm0), card_range] at this
      omega
    rw [prod_insert hm, card_insert_of_notMem hm]
    have ih' := ih h0'
    have hP : 0 ≤ ∏ d ∈ D, (1 + 1 / (d : ℝ)) := prod_nonneg fun d _ => by positivity
    have hc : ((D.card : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hcard
    have hc0 : (0 : ℝ) < (D.card : ℝ) + 1 := by positivity
    have h1 : 1 + 1 / (m : ℝ) ≤ 1 + 1 / ((D.card : ℝ) + 1) := by
      have := one_div_le_one_div_of_le hc0 hc
      linarith
    calc (1 + 1 / (m : ℝ)) * ∏ d ∈ D, (1 + 1 / (d : ℝ))
        ≤ (1 + 1 / ((D.card : ℝ) + 1)) * ((D.card : ℝ) + 1) :=
          mul_le_mul h1 ih' hP (by positivity)
      _ = ((D.card + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          field_simp
end Formalism.FourierDecayAlt.P.CutBP.JmuHC
