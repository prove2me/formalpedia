-- Prove2me | solution 1 for Formalism.L2.Th1.B.Mul.quad_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:15.675149+00:00
-- url     : https://prove2.me/submissions/a01e6846-d528-43a8-9656-9203cff2446a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_MultiplicationBiadditiveHolds
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Mul
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_zero')
variable {A : Type} [AddCommGroup A]
namespace Formalism.L2.Th1.B.Mul
theorem _root_.solution (g : ℤ → A) (h0 : g 0 = 0)
    (h : ∀ n m, g (n + m) + g (n - m) = g n + g n + g m + g m) (n : ℤ) :
    g n = (n ^ 2) • g 1 := by
  have ev : ∀ m, g (-m) = g m := by
    intro m
    have e := h 0 m
    rw [zero_add, zero_sub, h0] at e
    have e' : g (-m) = 0 + 0 + g m + g m - g m := eq_sub_of_add_eq' e
    rw [e']
    abel
  have nat : ∀ k : ℕ, g k = ((k : ℤ) ^ 2) • g 1 ∧ g ((k : ℤ) + 1) = (((k : ℤ) + 1) ^ 2) • g 1 := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have e := h ((k : ℤ) + 1) 1
      rw [add_sub_cancel_right, ih.1, ih.2] at e
      have e' := eq_sub_of_add_eq e
      push_cast
      rw [e']
      module
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact (nat k).1
  · rw [ev, (nat k).1, neg_sq]
end Formalism.L2.Th1.B.Mul
