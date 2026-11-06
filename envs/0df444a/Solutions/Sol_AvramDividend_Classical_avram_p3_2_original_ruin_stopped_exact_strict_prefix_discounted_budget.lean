-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_ruin_stopped_exact_strict_prefix_discounted_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:27:44.688094+00:00
-- url     : https://prove2.me/submissions/436741af-223c-4c3d-9311-ad7bd1867c54

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original-X/D discounted zero-atom source bound at the exact strict pre-ruin prefix cardinality, retaining the full filter equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (m : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let r : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    0 < τ → ∃ k : ℕ, k ≤ m + 1 ∧
      (Finset.range (m + 1)).filter (fun i => u (i + 1) < τ) = Finset.range k ∧
      u k < τ ∧
      rightLimit D 0 ω +
        (∑ i ∈ Finset.range k, r (i + 1) * cash i) +
        r k * post k ≤
      w x + (∑ i ∈ Finset.range k, r (i + 1) * source i) +
        ∑ i ∈ Finset.range k, (r (i + 1) - r i) * post i := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z
    else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  let r : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
  let cash : ℕ → ℝ := fun i =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  let post : ℕ → ℝ := fun i =>
    w (x + X.X (u i) ω - rightLimit D (u i) ω)
  let source : ℕ → ℝ := fun i =>
    V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
    V (x + X.X (u i) ω - rightLimit D (u i) ω)
  change 0 < τ → ∃ k : ℕ, k ≤ m + 1 ∧
      (Finset.range (m + 1)).filter (fun i => u (i + 1) < τ) = Finset.range k ∧
      u k < τ ∧
    rightLimit D 0 ω +
      (∑ i ∈ Finset.range k, r (i + 1) * cash i) +
      r k * post k ≤
    w x + (∑ i ∈ Finset.range k, r (i + 1) * source i) +
      ∑ i ∈ Finset.range k, (r (i + 1) - r i) * post i
  intro hτ
  obtain ⟨k, hk, hprefix, hstrict⟩ :=
    avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
      X x D T m ω
  have h0 : u 0 = 0 :=
    (avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω).1
  have hr0 : r 0 = 1 := by simp [r, h0]
  have hr : ∀ i : ℕ, i < k → 0 ≤ r (i + 1) := by
    intro i hi
    exact (Real.exp_pos _).le
  have hbudget :=
    avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget
      X x C hC hxc w hw_cont hw_smooth hw_grad
      D hD hjump ω q hq T m k r hr hr0
  have hb := hbudget (hstrict hτ)
  exact ⟨k, hk, hprefix, hstrict hτ, hb⟩

