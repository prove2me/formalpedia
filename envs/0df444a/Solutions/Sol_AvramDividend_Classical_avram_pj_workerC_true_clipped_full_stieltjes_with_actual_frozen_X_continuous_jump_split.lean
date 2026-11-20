-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_true_clipped_full_stieltjes_with_actual_frozen_X_continuous_jump_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:56:09.701818+00:00
-- url     : https://prove2.me/submissions/42b7d4b9-1a6f-440e-ac7c-4ea8c4239e64

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ρ : Ω → ℝ≥0)
    (n m : ℕ) (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    let Jp : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Yc : ℝ≥0 → ℝ := fun t => X.X t ω + Jp t
    let z : ℕ → ℝ := fun i => Y (u i)
    let c : ℕ → ℝ := fun i => Yc (u (i + 1)) - Yc (u i)
    let j : ℕ → ℝ := fun i => Jp (u (i + 1)) - Jp (u i)
    u (m + 1) = ρ ω ∧
    E (u (m + 1)) * w (Y (u (m + 1))) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
          E (u (i + 1)) *
            ((w (z i + c i - j i) - w (z i - j i)) +
              (w (z i - j i) - w (z i))) +
          E (u (i + 1)) *
            (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
          E (u (i + 1)) *
            (w (Y (u (i + 1))) -
              w (riskProcess X x D (u (i + 1)) ω))) := by
  intro Δ u E Y Z Jp Yc z c j
  obtain ⟨hEnd, hLedger⟩ :=
    avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
      X x q D hD.1.1 w ρ n m hρbound ω
  refine ⟨hEnd, ?_⟩
  have hSplit : ∀ i ∈ Finset.range (m + 1),
      w (Z i) - w (Y (u i)) =
        (w (z i + c i - j i) - w (z i - j i)) +
          (w (z i - j i) - w (z i)) := by
    intro i hi
    exact avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
      X x C D hD w ω u (m + 1) i (Finset.mem_range.mp hi)
  calc
    E (u (m + 1)) * w (Y (u (m + 1))) =
        w x + (w (x - rightLimit D 0 ω) - w x) +
          ∑ i ∈ Finset.range (m + 1),
            ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
              E (u (i + 1)) * (w (Z i) - w (Y (u i))) +
              E (u (i + 1)) *
                (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
              E (u (i + 1)) *
                (w (Y (u (i + 1))) -
                  w (riskProcess X x D (u (i + 1)) ω))) := hLedger
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hSplit i hi]
