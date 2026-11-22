-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_true_gradient_multiband_stopped_L2_zero_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:06:28.852385+00:00
-- url     : https://prove2.me/submissions/3d9453c5-6537-4a4b-8d67-18df5eb164bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_stopped_clipped_prejump_gradient_annulus_grid_L2_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (S : Finset ℕ) (cutLo cutHi : ℕ → ℕ)
    (hCut : ∀ i ∈ S, cutLo i ≤ cutHi i)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ j, grid j ≤ grid (j + 1))
    (n : ℕ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cutLo i : ℝ) + 1)))
        (-(1 / ((cutHi i : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s,
          X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
        (Ioc (grid j) (grid (j + 1)) ×ˢ B i)
    let r : ℕ → ℕ → ℝ := fun i j =>
      (((grid (j + 1) - grid j : ℝ≥0) : ℝ≥0∞) *
        X.ν (B i)).toReal
    let H : ℕ → Ω → ℝ := fun j ω =>
      max (-K) (min K (Real.exp (-(q * (grid j : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid j))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      ∑ j ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid j : WithTop ℝ≥0)
          then (0 : ℝ) else H j ω) * ((N i j ω).toReal - r i j)
    MemLp (fun ω => ∑ i ∈ S, Z i ω) 2 P ∧
      (∫ ω, ∑ i ∈ S, Z i ω ∂P) = 0 ∧
      (∀ ω, τ ω = 0 → ∑ i ∈ S, Z i ω = 0) := by
  classical
  intro B N r H Z
  have hOne (i : ℕ) (hi : i ∈ S) :
      MemLp (Z i) 2 P ∧ (∫ ω, Z i ω ∂P) = 0 := by
    simpa only [Z, H, N, r, B] using
      (avram_mix_annulus15_original_stopped_clipped_prejump_gradient_annulus_grid_L2_zero
        X x D hD w q K hK (cutLo i) (cutHi i)
        (hCut i hi) τ hτstop grid hGrid n)
  have hSum (F : Finset ℕ) (hF : F ⊆ S) :
      MemLp (fun ω => ∑ i ∈ F, Z i ω) 2 P ∧
        (∫ ω, ∑ i ∈ F, Z i ω ∂P) = 0 := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert i F hi ih =>
      have hiS : i ∈ S := hF (Finset.mem_insert_self i F)
      have hFS : F ⊆ S := Finset.Subset.trans (Finset.subset_insert i F) hF
      have hI := hOne i hiS
      have hR := ih hFS
      simp only [Finset.sum_insert hi]
      refine ⟨hI.1.add hR.1, ?_⟩
      have hIi : Integrable (Z i) P := hI.1.integrable (by norm_num)
      have hRi : Integrable (fun ω => ∑ j ∈ F, Z j ω) P :=
        hR.1.integrable (by norm_num)
      rw [integral_add hIi hRi, hI.2, hR.2]
      norm_num
  refine ⟨(hSum S (Finset.Subset.rfl)).1,
    (hSum S (Finset.Subset.rfl)).2, ?_⟩
  intro ω hzero
  change (∑ i ∈ S, ∑ j ∈ Finset.range n,
    (if (τ ω : WithTop ℝ≥0) ≤ (grid j : WithTop ℝ≥0)
      then (0 : ℝ) else H j ω) *
      ((N i j ω).toReal - r i j)) = 0
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hz : (τ ω : WithTop ℝ≥0) ≤ (grid j : WithTop ℝ≥0) := by
    simpa [hzero] using
      (show (0 : WithTop ℝ≥0) ≤ (grid j : WithTop ℝ≥0) from zero_le)
  rw [if_pos hz]
  simp
