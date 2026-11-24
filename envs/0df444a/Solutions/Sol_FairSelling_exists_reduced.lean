-- Prove2me | solution 1 for FairSelling.exists_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:19.459578+00:00
-- url     : https://prove2.me/submissions/5cf44c4a-b9f4-44af-8f8a-973fc50fb964

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Theorems.Thm_FairSelling_sum_le_vbarSum
import Theorems.Thm_FairSelling_reduce_to_one
import Theorems.Thm_FairSelling_exists_MMS_partition


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ),
      Config w p (MMS 2 w p) A s q ∧ s.card ≤ 1 := by
  obtain ⟨o, hovalid, hcover, hge⟩ := exists_MMS_partition (n := 2) (by norm_num) w p hw hp
  obtain ⟨hsold, hdisj, hmoney, hbudget⟩ := hovalid
  have hsum2 : ∑ j, o.money j = o.money 0 + o.money 1 := Fin.sum_univ_two _
  -- saturate the money: put the slack into part 0
  set slack : ℝ := (∑ g ∈ o.sold, p g) - o.money 0 - o.money 1 with hslack
  have hslack0 : 0 ≤ slack := by rw [hslack]; linarith [hbudget]
  have hcfg : Config w p (MMS 2 w p) o.kept o.sold ![o.money 0 + slack, o.money 1] := by
    refine ⟨fun i j hij => hdisj i j hij, fun i => hsold i, hcover, ?_, ?_, ?_⟩
    · rw [Fin.forall_fin_two]; constructor
      · simp only [Matrix.cons_val_zero]; linarith [hmoney 0]
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; exact hmoney 1
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hslack]; ring
    · rw [Fin.forall_fin_two]; constructor
      · simp only [Matrix.cons_val_zero]
        have h1 := hge 0; simp only [util] at h1
        linarith [sum_le_vbarSum w p (o.kept 0)]
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        have h1 := hge 1; simp only [util] at h1
        linarith [sum_le_vbarSum w p (o.kept 1)]
  exact reduce_to_one w p hp (MMS 2 w p) o.sold.card o.kept o.sold _ hcfg (le_refl _)
end FairSelling
