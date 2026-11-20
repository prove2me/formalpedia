-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_positive_ruin_topcap_pathwise_physical_mesh_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:01:54.776967+00:00
-- url     : https://prove2.me/submissions/065cd8fa-d7e4-4100-b73d-61c5db73a6c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_first_positive_stop_crossing_cell
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_crossing_cell_within_n_mesh_width
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_strict_prefix_earlier_stopped_grid_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_topcap_terminal_contact_cash_plus_prefix_source
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_ruin_contact_potential_sum_prefix_plus_one_cell
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_true_strict_prefix_stieltjes_error_le_ruin_rightLimit_mesh_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (ρ : ℝ≥0)
    (hρpos : 0 < ρ) (hρruin : (ρ : ℝ≥0∞) = ruinTime X x D ω)
    (n : ℕ) (hn : 0 < n) (hρn : ρ ≤ (n : ℝ≥0)) (j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    let m : ℕ := (n + 1) * (j + 1)
    let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
    let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range m,
        E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) +
      E ρ * (w (riskProcess X x D ρ ω) - w (Y ρ)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      q * ((n : ℝ) / ((j : ℝ) + 1)) *
        Real.exp (q * (n : ℝ)) * rightLimit D ρ ω +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
  let v : ℕ → ℝ≥0 := fun l =>
    min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let Z : ℕ → ℝ := fun l =>
    x + X.X (v (l + 1)) ω - rightLimit D (v l) ω
  obtain ⟨i, hi, hbefore, hcross⟩ :=
    avram_jump6_B_actual_canonical_first_positive_stop_crossing_cell
      n j ρ hρpos hρn
  let a : ℝ≥0 := v i
  have ha : a < ρ := hbefore
  have han : a ≤ (n : ℝ≥0) := (le_of_lt ha).trans hρn
  have hStrict : (a : ℝ≥0∞) < ruinTime X x D ω := by
    calc
      (a : ℝ≥0∞) < (ρ : ℝ≥0∞) := by exact_mod_cast ha
      _ = ruinTime X x D ω := hρruin
  have hWidth :=
    avram_jump6_B_canonical_crossing_cell_within_n_mesh_width
      n j i hn ρ hcross
  have hδ : (((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) : ℝ) =
      (n : ℝ) / ((j : ℝ) + 1) := by norm_num
  have hleft : (ρ : ℝ) -
      (((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) : ℝ) ≤ (a : ℝ) := by
    have hh : (ρ : ℝ) ≤ (a : ℝ) +
        (((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) : ℝ) := by
      exact_mod_cast hWidth
    linarith
  have hPre :=
    avram_jump6_B_original_topcap_strict_prefix_earlier_stopped_grid_cash
      X x C hC hTop q (le_of_lt hq) w hw_cont
      (hw_smooth.of_le (by norm_num)) hw_grad hxc D hD
      ω a ρ hStrict n j i han (Nat.le_of_lt hi) rfl
  have hEnd :=
    avram_jump6_B_topcap_terminal_contact_cash_plus_prefix_source
      X x C D hD hD.1.1 ω q (le_of_lt hq)
      ρ ((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) a
      hρpos hρruin hleft ha w hTop hw0 hw_cont hw_neg hw_grad
  have hSum :=
    avram_jump6_B_original_canonical_ruin_contact_potential_sum_prefix_plus_one_cell
      X x q D ω w n j i ρ hρn hi hcross
  have hErr :=
    avram_jump6_B_true_strict_prefix_stieltjes_error_le_ruin_rightLimit_mesh_rate
      D hD.1.1 ω a ρ (le_of_lt ha) q hq n hn j
  dsimp only at hPre hEnd hSum hErr ⊢
  rw [hSum]
  simp only [NNReal.coe_div, Nat.cast_add, Nat.cast_one] at hEnd
  have hv : v (i + 1) = ρ := hcross
  have hvi : v i = a := rfl
  rw [hcross]
  have hleftstop : min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ = a := rfl
  rw [hleftstop]
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
    NNReal.coe_one, Nat.cast_add, Nat.cast_one] at hEnd
  nlinarith only [hPre, hEnd, hErr]
