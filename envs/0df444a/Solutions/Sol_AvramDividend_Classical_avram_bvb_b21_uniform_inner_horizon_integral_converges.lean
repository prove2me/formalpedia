-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_uniform_inner_horizon_integral_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:49:27.158283+00:00
-- url     : https://prove2.me/submissions/40cff12b-94bd-4407-95fa-1340235343e2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

/-- The original shrinking terminal strip does not affect integrable cash. -/
theorem solution (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Icc 0 T) volume) :
    Tendsto
      (fun n : ℕ => ∫ t in Icc (0 : ℝ) (T - T / ((n : ℝ) + 2)), f t)
      atTop
      (𝓝 (∫ t in ⋃ n : ℕ, Icc (0 : ℝ) (T - T / ((n : ℝ) + 2)), f t)) := by
  let s : ℕ → Set ℝ := fun n => Icc 0 (T - T / ((n : ℝ) + 2))
  have hmono : Monotone s := by
    intro n m hnm
    have hcast : (n : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hnm
    have hden : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by
      linarith
    have hfrac : T / ((m : ℝ) + 2) ≤ T / ((n : ℝ) + 2) :=
      div_le_div_of_nonneg_left hT.le (by positivity) hden
    exact Icc_subset_Icc le_rfl (sub_le_sub_left hfrac T)
  have hsub : (⋃ n : ℕ, s n) ⊆ Icc (0 : ℝ) T := by
    intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨n, hn⟩
    change 0 ≤ t ∧ t ≤ T - T / ((n : ℝ) + 2) at hn
    refine ⟨hn.1, le_trans hn.2 ?_⟩
    exact sub_le_self _ (div_nonneg hT.le (by positivity))
  have hfi : IntegrableOn f (⋃ n : ℕ, s n) volume :=
    hf.mono_set hsub
  exact tendsto_setIntegral_of_monotone (fun n => measurableSet_Icc) hmono hfi
