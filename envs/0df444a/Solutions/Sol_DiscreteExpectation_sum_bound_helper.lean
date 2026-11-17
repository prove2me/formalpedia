-- Prove2me | solution 1 for DiscreteExpectation.sum_bound_helper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:32:04.520697+00:00
-- url     : https://prove2.me/submissions/ae93ecbc-9624-48ca-ab80-c779d84f0658

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F002
import Mathlib.Tactic
import Theorems.Thm_DiscreteExpectation_partition_telescope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DiscreteExpectation
open scoped BigOperators Pointwise Interval
noncomputable section

/-- Source monotonicity of the right-continuous step indicator. -/
private lemma source_step_mono {c : ℝ} : Monotone (stepIndicator c) := by
  intro x y hxy
  unfold stepIndicator
  split_ifs with h1 h2
  · rfl
  · exfalso; linarith
  · exact zero_le_one
  · rfl

theorem solution {a b : ℝ} (P : Partition a b) (c : ℝ) (ha : a < c) (hb : c < b)
    (vals : Fin P.n → ℝ) (hvals : ∀ i, vals i ∈ Partition.subinterval P i) :
    |∑ i : Fin P.n, vals i * (stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)) - c| ≤ P.mesh := by
  let Δ := fun (i : Fin P.n) => stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)

  have h_tele : ∑ i : Fin P.n, Δ i = 1 := by
    dsimp only [Δ]
    rw [partition_telescope]
    unfold stepIndicator
    have hb_gt : c ≤ b := by linarith
    have ha_lt : ¬(c ≤ a) := by linarith
    simp [hb_gt, ha_lt]

  -- Notice we swapped the sides of the equality!
  have h_c : ∑ i : Fin P.n, c * Δ i = c := by
    rw [← Finset.mul_sum, h_tele, mul_one]

  -- We use `calc` to completely isolate the rewrite steps!
  have h_diff : (∑ i : Fin P.n, vals i * Δ i) - c = ∑ i : Fin P.n, (vals i - c) * Δ i := by
    calc
      (∑ i : Fin P.n, vals i * Δ i) - c
        = (∑ i : Fin P.n, vals i * Δ i) - ∑ i : Fin P.n, c * Δ i := by rw [h_c]
      _ = ∑ i : Fin P.n, (vals i * Δ i - c * Δ i) := by rw [← Finset.sum_sub_distrib]
      _ = ∑ i : Fin P.n, (vals i - c) * Δ i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sub_mul]

  rw [h_diff]

  have h_abs_term : ∀ i : Fin P.n, |(vals i - c) * Δ i| = |vals i - c| * Δ i := by
    intro i
    rw [abs_mul]
    congr 1
    have h_strict : P.pts i.castSucc < P.pts i.succ := P.strict_mono Fin.castSucc_lt_succ
    -- `sub_nonneg.mpr` perfectly translates `A ≤ B` into `0 ≤ B - A`
    have hinc : 0 ≤ Δ i := sub_nonneg.mpr (source_step_mono h_strict.le)
    exact abs_of_nonneg hinc

  have h_abs : |∑ i : Fin P.n, (vals i - c) * Δ i| ≤ ∑ i : Fin P.n, |vals i - c| * Δ i := by
    calc
      |∑ i : Fin P.n, (vals i - c) * Δ i| ≤ ∑ i : Fin P.n, |(vals i - c) * Δ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin P.n, |vals i - c| * Δ i := Finset.sum_congr rfl (fun i _ => h_abs_term i)

  have h_le_mesh : ∑ i : Fin P.n, |vals i - c| * Δ i ≤ ∑ i : Fin P.n, P.mesh * Δ i := by
    apply Finset.sum_le_sum
    intro i _
    exact step_bound P c i (vals i) (hvals i)

  calc
    |∑ i : Fin P.n, (vals i - c) * Δ i| ≤ ∑ i : Fin P.n, |vals i - c| * Δ i := h_abs
    _ ≤ ∑ i : Fin P.n, P.mesh * Δ i := h_le_mesh
    _ = P.mesh := by rw [← Finset.mul_sum, h_tele, mul_one]
