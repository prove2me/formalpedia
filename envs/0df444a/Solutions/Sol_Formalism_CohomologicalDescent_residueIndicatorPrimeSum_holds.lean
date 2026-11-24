-- Prove2me | solution 1 for Formalism.CohomologicalDescent.residueIndicatorPrimeSum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:36.025871+00:00
-- url     : https://prove2.me/submissions/785401b2-3ac5-4f55-888f-fa703ccd9740

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_ContentDistanceBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Theorems.Thm_Formalism_CohomologicalDescent_eq_of_dvd_of_abs_lt_sq

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
theorem _root_.solution : ISum := by
  intro h L xm xp mB P hL hhL hmB hmx hxx hxh hP
  obtain ⟨P', hP'⟩ : ∃ P' : Finset ℕ,
      P' = P.filter (fun l : ℕ => ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB) := ⟨_, rfl⟩
  have hmem : ∀ l, l ∈ P' ↔ l ∈ P ∧ ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB := by
    intro l
    rw [hP', Finset.mem_filter]
  choose! g hg1 hg2 hg3 using fun l (hl : l ∈ P') => ((hmem l).mp hl).2
  have hh1 : (1 : ℝ) ≤ h := by
    have : (1 : ℤ) ≤ h := by omega
    exact_mod_cast this
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  have hterm : ∀ l ∈ P', Real.log (l : ℝ) ≤ Real.log (h : ℝ) := by
    intro l hl
    have hlP := ((hmem l).mp hl).1
    have hpos : 0 < g l - mB := by
      have := hg1 l hl
      omega
    have hdle : (l : ℤ) ≤ g l - mB := Int.le_of_dvd hpos (hg3 l hl)
    have hle : (l : ℤ) ≤ h := by
      have := hg2 l hl
      omega
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (hP l hlP).1.pos
    exact Real.log_le_log hl0 (by exact_mod_cast hle)
  have hcard : P'.card ≤ (Finset.Icc xm xp).card := by
    apply Finset.card_le_card_of_injOn g
    · intro l hl
      exact Finset.mem_Icc.mpr ⟨hg1 l hl, hg2 l hl⟩
    · intro l hl l' hl' heq
      have hlP := ((hmem l).mp hl).1
      have hlP' := ((hmem l').mp hl').1
      have hpos : 0 < g l - mB := by
        have := hg1 l hl
        omega
      have hlt : ((|g l - mB| : ℤ) : ℝ) < L ^ 2 := by
        have h1 : |g l - mB| ≤ (h : ℤ) := by
          rw [abs_of_pos hpos]
          have := hg2 l hl
          omega
        have h2 : ((|g l - mB| : ℤ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast h1
        linarith
      refine eq_of_dvd_of_abs_lt_sq hL hpos.ne' hlt (hP l hlP).1 (hP l' hlP').1 (hP l hlP).2
        (hP l' hlP').2 (hg3 l hl) ?_
      rw [heq]
      exact hg3 l' hl'
  have hcardR : ((Finset.Icc xm xp).card : ℝ) = ((xp - xm : ℤ) : ℝ) + 1 := by
    have h0 : (0 : ℤ) ≤ xp + 1 - xm := by omega
    rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg h0]
    push_cast
    ring
  have key : ∑ l ∈ P', Real.log (l : ℝ) ≤ (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ) := by
    calc ∑ l ∈ P', Real.log (l : ℝ) ≤ ∑ _l ∈ P', Real.log (h : ℝ) := Finset.sum_le_sum hterm
      _ = (P'.card : ℝ) * Real.log (h : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Finset.Icc xm xp).card : ℝ) * Real.log (h : ℝ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlogh
      _ = (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ) := by rw [hcardR]
  refine Eq.trans_le ?_ key
  rw [hP', Finset.sum_filter]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold IlInd
  split_ifs <;> simp
end Formalism.CohomologicalDescent
