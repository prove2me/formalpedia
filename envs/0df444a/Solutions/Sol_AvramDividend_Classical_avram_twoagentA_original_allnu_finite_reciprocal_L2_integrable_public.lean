-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:23:42.863265+00:00
-- url     : https://prove2.me/submissions/42a47af8-2782-4c0b-a56a-c501256f0612

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_finite_borel_mark_simple_sum_square_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let S : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    Integrable (fun ω => (S ω) ^ 2) P := by
  classical
  let B : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let S : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.Ico n m,
      (-(1 / ((i : ℝ) + 1))) *
        ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
  let Bshift : ℕ → Set ℝ := fun j => B (n + j)
  let cshift : ℕ → ℝ := fun j => -(1 / (((n + j : ℕ) : ℝ) + 1))
  have hBm : ∀ i ∈ Finset.range (m - n), MeasurableSet (Bshift i) := by
    intro i hi
    exact measurableSet_Ioc
  have hSep : ∀ i ∈ Finset.range (m - n),
      Bshift i ⊆ Iic (-(1 / ((m : ℝ) + 1))) := by
    intro i hi z hz
    have him : i < m - n := Finset.mem_range.mp hi
    have hBound : n + i + 2 ≤ m + 1 := by omega
    have hCast : (((n + i : ℕ) : ℝ) + 2) ≤ (m : ℝ) + 1 := by
      exact_mod_cast hBound
    have hInv := one_div_le_one_div_of_le
      (show 0 < (((n + i : ℕ) : ℝ) + 2) by positivity) hCast
    have hNeg : -(1 / (((n + i : ℕ) : ℝ) + 2)) ≤
        -(1 / ((m : ℝ) + 1)) := by linarith
    exact le_trans hz.2 hNeg
  have hS2 :=
    avram_ja34_original_finite_borel_mark_simple_sum_square_integrable
      X T m (m - n) Bshift cshift hBm hSep
  simpa [S, B, NX, r, Bshift, cshift,
    Finset.sum_Ico_eq_sum_range, add_comm, add_left_comm, add_assoc] using hS2
