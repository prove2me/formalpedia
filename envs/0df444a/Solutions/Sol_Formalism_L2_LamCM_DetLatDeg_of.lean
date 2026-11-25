-- Prove2me | solution 1 for Formalism.L2.LamCM.DetLatDeg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:01.516462+00:00
-- url     : https://prove2.me/submissions/ad42bed1-d67e-44b1-b851-8118b97b9788

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_A2_deg_detLine
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_ne_zero
import Theorems.Thm_Formalism_L2_LamCM_detLineFree
import Theorems.Thm_P2M_Formalism_L2_LamCM_A2_absNorm_pos__7ef009ed3ead
import Theorems.Thm_P2M_Formalism_L2_LamCM_absNorm_pos__34243083059c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
namespace Formalism.L2.LamCM
theorem _root_.solution : IndexFormula → DetLatDeg := by
  intro hIF K _ _ m L b hL hb
  set M0 := Submodule.span (𝓞 K) (Set.range b) with hM0
  let L0 : MLat K m := ⟨M0, L.H⟩
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    rcases isEmpty_or_nonempty (Fin m) with hm | hm
    · exact eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact zero_mem _
    · exact hb.2.1.span_eq_top_of_card_eq_finrank (by simp)
  have hL0 : L0.Good := by
    refine ⟨Submodule.fg_span (Set.finite_range b), ?_, hL.2.2⟩
    show Submodule.span K ((M0 : Set (Fin m → K))) = ⊤
    rw [hM0, Submodule.span_span_of_tower]
    exact hspan
  have hfree := detLineFree K m L0 b hL0 rfl
  have hI := hIF K m L.M b hL.1 hL.2.1 hb.2.1 hb.1
  have e0 : (MLat.mk M0 (fun _ => 0) : MLat K m).detIdeal = L0.detIdeal := rfl
  have e1 : (MLat.mk L.M (fun _ => 0) : MLat K m).detIdeal = L.detIdeal := rfl
  rw [e0, e1] at hI
  have hpos0 : (0 : ℝ) < ((FractionalIdeal.absNorm L0.detIdeal : ℚ) : ℝ) := by
    exact_mod_cast A2.absNorm_pos' (A2.detIdeal_ne_zero L0 hL0)
  have hpos : (0 : ℝ) < ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) := by
    exact_mod_cast A2.absNorm_pos' (A2.detIdeal_ne_zero L hL)
  have hrel : (0 : ℝ) < (M0.toAddSubgroup.relIndex L.M.toAddSubgroup : ℝ) := by
    rcases (Nat.cast_nonneg (α := ℝ) (M0.toAddSubgroup.relIndex L.M.toAddSubgroup)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hI; linarith
  rw [A2.deg_detLine] at hfree ⊢
  have hlog : Real.log ((FractionalIdeal.absNorm L0.detIdeal : ℚ) : ℝ) =
      Real.log (M0.toAddSubgroup.relIndex L.M.toAddSubgroup : ℝ) + Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) := by
    rw [hI, Real.log_mul hrel.ne' hpos.ne']
  have hH : L0.H = L.H := rfl
  rw [hH] at hfree
  unfold ReciprocityTheory.MultiplicativeHeights.latDeg
  rw [← hM0]
  linarith
end Formalism.L2.LamCM
