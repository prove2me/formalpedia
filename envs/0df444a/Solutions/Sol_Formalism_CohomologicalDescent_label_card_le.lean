-- Prove2me | solution 1 for Formalism.CohomologicalDescent.label_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:51.987739+00:00
-- url     : https://prove2.me/submissions/b254ad60-005e-43f4-894f-ef67b14e30ed

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse

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
theorem _root_.solution {l : ℕ} (hl0 : 0 < l) (xm xp mB : ℤ) (hx : xm ≤ xp) :
    ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ)
      ≤ ((xp - xm : ℤ) : ℝ) / l + 1 := by
  have hl : (0 : ℤ) < l := by exact_mod_cast hl0
  have hq0 : 0 ≤ (xp - xm) / (l : ℤ) := Int.ediv_nonneg (by linarith) hl.le
  have hcard : ((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card ≤
      (Finset.Icc (0 : ℤ) ((xp - xm) / (l : ℤ))).card := by
    refine Finset.card_le_card_of_injOn (fun x => (x - xm) / (l : ℤ)) ?_ ?_
    · intro x hx
      simp only [Finset.coe_Icc, Finset.coe_filter, Set.mem_Icc, Set.mem_ofPred_eq,
        Finset.mem_Icc] at hx ⊢
      exact ⟨Int.ediv_nonneg (by linarith) hl.le, Int.ediv_le_ediv hl (by linarith)⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc] at hx hy
      have hxy' : (x - xm) / (l : ℤ) = (y - xm) / (l : ℤ) := hxy
      have hmod : (x - xm) % (l : ℤ) = (y - xm) % (l : ℤ) := by
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        apply Int.emod_eq_zero_of_dvd
        have e : (x - xm) - (y - xm) = (x - mB) - (y - mB) := by ring
        rw [e]
        exact dvd_sub hx.2 hy.2
      have e1 : (l : ℤ) * ((x - xm) / (l : ℤ)) + (x - xm) % (l : ℤ) = x - xm := by
        exact Int.mul_ediv_add_emod _ _
      have e2 : (l : ℤ) * ((y - xm) / (l : ℤ)) + (y - xm) % (l : ℤ) = y - xm := by
        exact Int.mul_ediv_add_emod _ _
      rw [hxy', hmod] at e1
      linarith
  have hIcc : ((Finset.Icc (0 : ℤ) ((xp - xm) / (l : ℤ))).card : ℤ) = (xp - xm) / (l : ℤ) + 1 := by
    rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
    ring
  have hqr : (((xp - xm) / (l : ℤ) : ℤ) : ℝ) ≤ ((xp - xm : ℤ) : ℝ) / l := by
    rw [le_div_iff₀ (by exact_mod_cast hl0 : (0 : ℝ) < l)]
    have := Int.ediv_mul_le (xp - xm) (ne_of_gt hl)
    exact_mod_cast this
  have hc : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℤ) ≤
      (xp - xm) / (l : ℤ) + 1 := by
    rw [← hIcc]
    exact_mod_cast hcard
  have hcR : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ) ≤
      (((xp - xm) / (l : ℤ) : ℤ) : ℝ) + 1 := by
    exact_mod_cast hc
  linarith
end Formalism.CohomologicalDescent
