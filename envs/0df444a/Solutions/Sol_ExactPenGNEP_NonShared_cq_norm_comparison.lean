-- Prove2me | solution 1 for ExactPenGNEP.NonShared.cq_norm_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:42:07.003057+00:00
-- url     : https://prove2.me/submissions/615e5a94-0cef-46e6-94f1-0b03266b4800

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting

open LeiBR.Sync

lemma epg_sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {t : ℝ} (ht : 1 ≤ t) : ∑ i ∈ s, a i ^ t ≤ (∑ i ∈ s, a i) ^ t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow (by linarith : t ≠ 0)]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hs : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg (fun i _ => ha i)
    calc a j ^ t + ∑ i ∈ s, a i ^ t ≤ a j ^ t + (∑ i ∈ s, a i) ^ t := by linarith
      _ ≤ (a j + ∑ i ∈ s, a i) ^ t := Real.add_rpow_le_rpow_add (ha j) hs ht

theorem solution (q : ℝ) (hq : 1 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (v : Fin k → ℝ),
      c * (∑ i, |v i| ^ q) ^ (1 / q) ≤ (∑ i, |v i| ^ (q - 1)) ^ (1 / (q - 1)) := by
  refine ⟨1, one_pos, fun k v => ?_⟩
  rw [one_mul]
  have hp : 0 < q - 1 := by linarith
  set a : Fin k → ℝ := fun i => |v i| ^ (q - 1) with ha_def
  have ha : ∀ i, 0 ≤ a i := fun i => Real.rpow_nonneg (abs_nonneg _) _
  set t : ℝ := q / (q - 1) with ht_def
  have ht : 1 ≤ t := by rw [ht_def, le_div_iff₀ hp]; linarith
  have hq0 : 0 < q := by linarith
  have hat : ∀ i, a i ^ t = |v i| ^ q := by
    intro i
    rw [ha_def]; dsimp only
    rw [← Real.rpow_mul (abs_nonneg _), ht_def, mul_div_cancel₀ _ hp.ne']
  have key : ∑ i, |v i| ^ q ≤ (∑ i, a i) ^ t := by
    have := epg_sum_rpow_le_rpow_sum Finset.univ a ha ht
    simpa [hat] using this
  have hS : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
  calc (∑ i, |v i| ^ q) ^ (1 / q) ≤ ((∑ i, a i) ^ t) ^ (1 / q) :=
        Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) key
          (by positivity)
    _ = (∑ i, a i) ^ (1 / (q - 1)) := by
        rw [← Real.rpow_mul hS, ht_def]
        congr 1
        field_simp
