-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_finite_simple_L1_completion_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:42:16.26187+00:00
-- url     : https://prove2.me/submissions/676e08ac-3054-41f5-b30d-06260deb2924

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_centered_limit_of_L1_convergence
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_finite_simple_centering_of_cell_compensation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The L¹ limit of genuinely compensated finite simple original-space
jump sums remains centred. All source cell and convergence data are explicit. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : ℕ → Finset ι) (J C : ι → Ω → ℝ) (a : ℕ → ι → ℝ)
    (M : Ω → ℝ)
    (hJI : ∀ n, ∀ i ∈ S n, Integrable (J i) P)
    (hCI : ∀ n, ∀ i ∈ S n, Integrable (C i) P)
    (hCells : ∀ n, ∀ i ∈ S n,
       (∫ ω, J i ω ∂P) = (∫ ω, C i ω ∂P))
    (hMI : Integrable M P)
    (hConv : Tendsto
      (fun n => ∫⁻ ω,
        ‖(∑ i ∈ S n, a n i * (J i ω - C i ω)) - M ω‖ₑ ∂P)
      atTop (𝓝 0)) :
    (∫ ω, M ω ∂P) = 0 := by
  have hStep (n : ℕ) :
      Integrable (fun ω => ∑ i ∈ S n, a n i * (J i ω - C i ω)) P ∧
      (∫ ω, ∑ i ∈ S n, a n i * (J i ω - C i ω) ∂P) = 0 := by
    exact AvramDividend.Classical.avram_p4_b_smalljump_finite_simple_centering_of_cell_compensation
      (S n) J C (a n) (hJI n) (hCI n) (hCells n)
  exact AvramDividend.Classical.avram_p4_b_smalljump_centered_limit_of_L1_convergence
    (fun n ω => ∑ i ∈ S n, a n i * (J i ω - C i ω)) M
    (fun n => (hStep n).1) hMI (fun n => (hStep n).2) hConv