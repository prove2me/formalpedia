-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_localised_discounted_C1_mesh_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:34:55.879903+00:00
-- url     : https://prove2.me/submissions/0f66dc19-07e0-4ce3-be8b-e6b9ab400354

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_finite_grid_C1_two_stage_error
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_two_stage_mesh_error_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (n : ℕ → ℕ)
    (u : Ω → ℕ → ℕ → ℝ≥0)
    (S : Ω → ℕ → Finset ℕ)
    (hGrid : ∀ ω k i, i < n k → u ω k i ≤ u ω k (i + 1))
    (hZero : ∀ ω k, u ω k 0 = 0)
    (hEnd : ∀ ω k, u ω k (n k) = τ ω) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let c : ℕ → ℕ → ℝ := fun k i =>
        Y (u ω k (i + 1)) - Y (u ω k i)
      let j : ℕ → ℕ → ℝ := fun k i =>
        J (u ω k (i + 1)) - J (u ω k i)
      let d : ℕ → ℕ → ℝ := fun k i =>
        X.X (u ω k (i + 1)) ω - X.X (u ω k i) ω
      let z : ℕ → ℕ → ℝ := fun k i =>
        x + X.X (u ω k i) ω - rightLimit D (u ω k i) ω
      let e : ℕ → ℕ → ℝ := fun k i =>
        Real.exp (-(q * (u ω k i : ℝ)))
      let tail : ℕ → ℝ := fun k =>
        ∑ i ∈ Finset.range (n k),
          if i ∈ S ω k then |c k i| else |j k i|
      let err : ℕ → ℝ := fun k =>
        ∑ i ∈ Finset.range (n k),
          e k i * ((w (z k i + d k i) - w (z k i)) -
            (w (z k i - j k i) - w (z k i)) -
            deriv w (z k i) * c k i)
      let B : ℝ := |X.drift| * (τ ω : ℝ) + (R (τ ω) - R 0)
      ∀ (ε : ℕ → ℝ) (K : ℝ),
        (∀ k, 0 ≤ ε k) → 0 ≤ K →
        (∀ k i, i < n k →
          |w (z k i + c k i) - w (z k i) -
            deriv w (z k i) * c k i| ≤ ε k * |c k i|) →
        (∀ k i, i < n k → i ∈ S ω k →
          |w (z k i + c k i - j k i) - w (z k i - j k i)| ≤
              K * |c k i| ∧
          |w (z k i + c k i) - w (z k i)| ≤ K * |c k i|) →
        (∀ k i, i < n k → i ∉ S ω k →
          |w (z k i + c k i - j k i) - w (z k i + c k i)| ≤
              K * |j k i| ∧
          |w (z k i - j k i) - w (z k i)| ≤ K * |j k i|) →
        Filter.Tendsto ε Filter.atTop (nhds 0) →
        Filter.Tendsto tail Filter.atTop (nhds 0) →
        (∀ k, |err k| ≤ ε k * B + 2 * K * tail k) ∧
          Filter.Tendsto err Filter.atTop (nhds 0) := by
  filter_upwards
    [avram_p3_main_original_jump_removed_grid_variation X hBV] with ω hω
  intro J R Y c j d z e tail err B
  intro ε K hε hK htaylor hlarge hsmall hεlim htaillim
  have hr (k : ℕ) : ∀ i, i < n k → 0 ≤ e k i ∧ e k i ≤ 1 := by
    intro i hi
    have hnonneg : 0 ≤ q * (u ω k i : ℝ) :=
      mul_nonneg hq (u ω k i).property
    constructor
    · exact (Real.exp_pos _).le
    · dsimp only [e]
      calc
        Real.exp (-(q * (u ω k i : ℝ))) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr hnonneg)
        _ = 1 := Real.exp_zero
  have hbound (k : ℕ) :
      |err k| ≤ ε k * B + 2 * K * tail k := by
    have hstep : ∀ i, i < n k → d k i = c k i - j k i := by
      intro i hi
      dsimp [d, c, j, Y]
      ring
    have hvar : (∑ i ∈ Finset.range (n k), |c k i|) ≤ B := by
      have hvar0 := hω (n k) (u ω k) (hGrid ω k)
      simpa only [c, B, J, R, Y, hZero ω k, hEnd ω k,
        NNReal.coe_zero, sub_zero] using hvar0
    have hcalc :=
      avram_p3_main_original_finite_grid_C1_two_stage_error
        (n k) (S ω k) w (e k) (z k) (c k) (j k) (d k)
        (ε k) B K (hε k) hK hstep (hr k)
        (htaylor k) hvar (hlarge k) (hsmall k)
    simpa only [err, tail] using hcalc
  exact ⟨hbound,
    avram_p3_main_original_two_stage_mesh_error_limit
      err ε tail B K hεlim htaillim hbound⟩
