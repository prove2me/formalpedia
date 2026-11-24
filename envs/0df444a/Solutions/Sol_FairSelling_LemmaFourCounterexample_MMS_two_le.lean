-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.MMS_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:08:47.711723+00:00
-- url     : https://prove2.me/submissions/c1f08a3b-2f1e-4fa9-a6f2-e0cc61bb5838

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
import Theorems.Thm_FairSelling_LemmaFourCounterexample_cashVal_eq
import Theorems.Thm_FairSelling_LemmaFourCounterexample_cashPrice_eq
import Theorems.Thm_FairSelling_LemmaFourCounterexample_no_two_bundles
import Theorems.Thm_FairSelling_MMSset_nonempty


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample
namespace FairSelling.LemmaFourCounterexample
theorem _root_.solution : MMS 2 (cashVal R w) (cashPrice R p 0) ≤ 37 := by
  refine csSup_le (MMSset_nonempty _ _) ?_
  rintro r ⟨o, ⟨-, hdisj, hmoney, hbudget⟩, hr⟩
  have hprice : ∑ g ∈ o.sold, cashPrice R p 0 g = 0 :=
    Finset.sum_eq_zero (fun g _ => cashPrice_eq g)
  have hsum0 : ∑ j, o.money j = 0 := by
    rw [hprice] at hbudget
    exact le_antisymm hbudget (Finset.sum_nonneg fun j _ => hmoney j)
  have hmz : ∀ j, o.money j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hmoney j)).mp hsum0 j (Finset.mem_univ j)
  have hutil : ∀ j, util (cashVal R w) o j = ((∑ x ∈ o.kept j, cwn x : ℕ) : ℝ) := by
    intro j
    rw [util, hmz j, add_zero]
    push_cast
    exact Finset.sum_congr rfl (fun x _ => cashVal_eq x)
  rcases no_two_bundles (o.kept 0) (o.kept 1) (hdisj 0 1 (by decide)) with h | h
  · have h1 := hr 0
    rw [hutil 0] at h1
    have h2 : ((∑ x ∈ o.kept 0, cwn x : ℕ) : ℝ) ≤ 37 := by exact_mod_cast h
    linarith
  · have h1 := hr 1
    rw [hutil 1] at h1
    have h2 : ((∑ x ∈ o.kept 1, cwn x : ℕ) : ℝ) ≤ 37 := by exact_mod_cast h
    linarith
end FairSelling.LemmaFourCounterexample
