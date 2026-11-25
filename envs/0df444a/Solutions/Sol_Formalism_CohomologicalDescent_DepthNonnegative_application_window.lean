-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.application_window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:00.582255+00:00
-- url     : https://prove2.me/submissions/6b21bd41-47bb-4e01-9236-d00e023469cc

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_LD_applicationSteps
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expLeMono
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_labelRHSPlus_shift_invariant
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_second_valuation_up_to_holds
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
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : ApplicationWindow := by
  intro hD l k j t q h lam xm xp hl ht hanti hconst hspread hh hcloud hlows habove hle htop ecl hecl I μ hμ
  refine expLeMono l _ _ μ _ _ ?_
    (applicationSteps hD l k j t q h lam hl ht hanti hconst hspread ecl hecl I μ hμ)
  refine Nat.le_floor ?_
  have hb : ∀ a : Fin (k + j), lam (k + j) ≤ res (k + j) lam a ∧ res (k + j) lam a ≤ lam 0 := fun a =>
    ⟨hanti a.val (k + j) (by have := a.isLt; omega) (by omega),
      hanti 0 a.val (Nat.zero_le _) (by have := a.isLt; omega)⟩
  have eU : ∀ a : Fin (k + j),
      UN (k + j + t + q) lam a.val = U k j t (res (k + j) lam) a + (q : ℤ) := by
    intro a
    unfold UN U res
    push_cast
    ring
  have e3 : UN (k + j + t + q) lam (k + j) = maxB t (lam (k + j)) + (q : ℤ) := by
    unfold UN maxB
    push_cast
    ring
  have hR : Rows k j t (lam (k + j)) (lam 0) (res (k + j) lam) (xm - q) (xp - q) := by
    refine ⟨fun a => (hb a).1, fun a => (hb a).2, ?_, ?_, ?_, ?_⟩
    · intro a ha
      have h1 := hcloud a.val ha
      rw [eU a] at h1
      constructor <;> omega
    · intro a ha
      have h1 := hlows a.val ha a.isLt
      rw [eU a] at h1
      omega
    · rw [e3] at habove
      omega
    · omega
  have hxp : (xp - q) - maxB t (lam (k + j)) ≤ (h : ℤ) := by
    rw [e3] at htop
    omega
  have hh1 : 1 ≤ h := by omega
  have hcost : (blockCost l (k + j) t I lam : ℝ) ≤ (j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) +
      labelSumBoundPos l k t h (I : ℝ) (xm - q) (xp - q) (maxB t (lam (k + j))) := by
    unfold blockCost
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (I + 1)) ⟨0, by simp⟩
      (fun i => padicValInt l (Dn t (lam 0 - lam (k + j)) i fun b : Fin (k + j) =>
        lam 0 - res (k + j) lam (Fin.rev b)))
    rw [heq]
    exact second_valuation_up_to_holds l k j t (lam (k + j)) (lam 0) h i (I : ℝ) (res (k + j) lam) _ _ hl hR hxp hh
      (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hP : (((h - 1) / (l - 1) : ℕ) : ℝ) ≤ ((h : ℝ) - 1) / ((l : ℝ) - 1) := by
    have h1 := Nat.cast_div_le (α := ℝ) (m := h - 1) (n := l - 1)
    have hl2 := hl.two_le
    rw [Nat.cast_sub hh1, Nat.cast_sub (by omega : 1 ≤ l)] at h1
    simpa using h1
  have hs := labelRHSPlus_shift_invariant l k t h (I : ℝ) (xm - q) (xp - q) (maxB t (lam (k + j))) q
  rw [sub_add_cancel, sub_add_cancel] at hs
  unfold cPrime
  rw [e3, hs]
  have hq := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))
  have hj := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  push_cast
  linarith
end Formalism.CohomologicalDescent.DepthNonnegative
