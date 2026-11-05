-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_stopped_closed_cash_generator_budget_up_to_mesh_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:13:47.155258+00:00
-- url     : https://prove2.me/submissions/99b61b49-f904-4440-992a-24650e1f9821

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_closed_cash_C1_generator_drift_raw_J_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_source_C1_two_errors_joint_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_compact_reserve_band_implies_cap_safe_drift
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_raw_cell_eq_cumulative_J_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original stopped closed cash is dominated by physical generator drift, genuine raw J and arbitrarily small joint C1 mesh error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_open : IsOpen {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hb : C = ⊤ ∨ b < C.toReal)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      ∀ (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let Y : ℝ≥0 → ℝ := fun t =>
          x + X.X t ω - rightLimit D t ω
        let z : ℕ → ℕ → ℝ := fun m i => Y (u m i)
        let c : ℕ → ℕ → ℝ := fun m i =>
          ((u m (i + 1) : ℝ) - (u m i : ℝ)) * X.drift
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, Monotone (u m)) →
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m →
          u m (i + 1) = 0 ∨
          (u m (i + 1) : ℝ≥0∞) < ruinTime X x D ω) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
            (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) →
        (∀ m i, i < n m → z m i ≤ b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i - j m i) (z m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i + c m i - j m i)
            (z m i + c m i) ⊆ Set.Icc a b) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            E T * w (Y T) +
              (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
                ENNReal.ofReal (Real.exp (-(q * s)))
                  ∂(dividendMeasure D ω)).toReal ≤
            w x +
              (∑ i ∈ Finset.range (n m),
                (E (u m (i + 1)) - E (u m i)) *
                  V (Y (u m (i + 1)))) +
              (∑ i ∈ Finset.range (n m),
                E (u m i) * (deriv w (z m i) * c m i)) +
              (∑ i ∈ Finset.range (n m),
                E (u m i) * (w (z m i - j m i) - w (z m i))) + η := by
  intro V E
  have hCash :=
    avram_p3_2_original_closed_cash_C1_generator_drift_raw_J_budget
      X hBV x hx C hC hxc q hq w hw_cont hw_smooth hw_grad D hD
  have hJoint :=
    avram_p3_2_original_physical_source_C1_two_errors_joint_mesh_vanish
      X hBV w C hw_smooth hw_open a b hBand q hq
  have hRaw :=
    avram_p3_2_original_raw_cell_eq_cumulative_J_increment X hBV
  filter_upwards [hCash, hJoint, hRaw] with ω hω hJointω hRawω
  intro J T u n Y z c j hMono hStart hEnd hPre hClock hCeil
    hTaylorBand hJumpBase hJumpShift η hη
  have hGrid : ∀ m i, i < n m →
      u m i ≤ u m (i + 1) := by
    intro m i hi
    exact hMono m (Nat.le_succ i)
  have hCap :=
    avram_p3_2_original_physical_compact_reserve_band_implies_cap_safe_drift
      X x D ω C b hb u n hGrid hCeil hClock
  have hJointBound :=
    hJointω x D T u n hStart hEnd hGrid
      hClock hTaylorBand hJumpBase hJumpShift η hη
  have hJumpEq (m i : ℕ) :
      (∑' v : ℝ≥0,
        if u m i < v ∧ v ≤ u m (i + 1) then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0) = j m i := by
    have hi : i < i + 1 := Nat.lt_succ_self _
    have h :=
      hRawω (u m) (i + 1)
        (fun k hk => hMono m (Nat.le_succ k)) i hi
    simpa only [j] using h
  filter_upwards [hCap, hJointBound] with m hCapm hError
  have hSource := hω (u m) (n m)
    (hMono m) (hStart m) (hPre m) hCapm
  dsimp only at hSource hError ⊢
  simp_rw [hJumpEq] at hSource
  rw [hEnd m] at hSource
  have hErrUpper :
      (∑ i ∈ Finset.range (n m),
        E (u m i) *
          (w (z m i + c m i) - w (z m i) -
            deriv w (z m i) * c m i)) +
      (∑ i ∈ Finset.range (n m),
        E (u m i) *
          (w (z m i + c m i - j m i) - w (z m i + c m i) -
            w (z m i - j m i) + w (z m i))) < η := by
    exact lt_of_le_of_lt (le_abs_self _) hError
  linarith [hSource, hErrUpper]
