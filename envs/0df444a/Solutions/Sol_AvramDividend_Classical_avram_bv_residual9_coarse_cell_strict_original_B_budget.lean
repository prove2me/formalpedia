-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_coarse_cell_strict_original_B_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:53:11.485356+00:00
-- url     : https://prove2.me/submissions/9a3dd2d6-2dbc-4964-9ed3-9c798b20ef97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_stopped_derivative_R_mesh_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under an active negative generator gap, a collapsed physical row has
strict negative source-exact B budget; the BV raw R term is nonpositive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hprefix : ∀ i, i ≤ n → u n i = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hactive : ∀ᵐ ω ∂P,
      (u n n : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n n) ∧
      ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n n)) < C)
    (hnegative : ∀ᵐ ω ∂P,
      X.generator w (Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n n)) -
      q * w (Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n n)) ≤ -ε) :
    ∀ᵐ ω ∂P,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))) ≤
      -ε * (u n (n + 1) : ℝ) := by
  have hR := avram_bv_residual10_original_stopped_derivative_R_mesh_nonpositive
    X hBV q C w hw_grad x D u n hu
  filter_upwards [hR, hactive, hnegative] with ω hRω hAct hNeg
  dsimp only
  have hcell (i : ℕ) (hi : i < n) :
      (u n (i + 1) : ℝ) - (u n i : ℝ) = 0 := by
    rw [hprefix i (Nat.le_of_lt hi),
      hprefix (i + 1) (Nat.succ_le_of_lt hi)]
    norm_num
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i)) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i)) -
             q * w (Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i))) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) =
      (X.generator w (Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n n)) -
       q * w (Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n n))) *
      (u n (n + 1) : ℝ) := by
    rw [Finset.sum_range_succ]
    have hzero : (∑ i ∈ Finset.range n,
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i)) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i)) -
           q * w (Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i))) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      split_ifs <;> simp [hcell i (Finset.mem_range.mp hi)]
    rw [hzero, zero_add]
    rw [if_pos hAct, hprefix n le_rfl]
    simp
  dsimp at hRω
  rw [hsum]
  have hlen : 0 ≤ (u n (n + 1) : ℝ) := NNReal.coe_nonneg _
  have hmul :
      (X.generator w (Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n n)) -
       q * w (Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n n))) *
        (u n (n + 1) : ℝ) ≤
      -ε * (u n (n + 1) : ℝ) :=
    mul_le_mul_of_nonneg_right hNeg hlen
  linarith
