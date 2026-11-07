-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_original_physical_prefix_cofinal_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:31:00.735552+00:00
-- url     : https://prove2.me/submissions/c4ffbbfc-a146-4bad-b367-4fe2130d5db8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_natural_inner_clock_delta_certificate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

/- Exact cofinality of the original physical strict-prefix horizon. -/
theorem solution
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let v : ℕ → ℝ := fun n => T - δ n
    Monotone v ∧ (∀ n, 0 ≤ v n) ∧ (∀ n, v n ≤ T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < v n) := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let v : ℕ → ℝ := fun n => T - δ n
  change Monotone v ∧ (∀ n, 0 ≤ v n) ∧ (∀ n, v n ≤ T) ∧
    (∀ s : ℝ, s < T → ∃ n, s < v n)
  rcases avram_bv_strict6_natural_inner_clock_delta_certificate T hT with
    ⟨hδpos, hδle, hδanti, hδtendsto⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact sub_le_sub_left (hδanti hab) T
  · intro n
    exact sub_nonneg.mpr (hδle n)
  · intro n
    exact sub_le_self T (le_of_lt (hδpos n))
  · have hvlim : Tendsto v atTop (𝓝 T) := by
      simpa [v, δ] using (tendsto_const_nhds.sub hδtendsto)
    intro s hs
    exact (hvlim.eventually (isOpen_Ioi.mem_nhds hs)).exists
