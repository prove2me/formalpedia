-- Prove2me | solution 4 for AvramDividend.Classical.avram_bv_residual9_original_arbitrary_generator_sum_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:11:04.287202+00:00
-- url     : https://prove2.me/submissions/81654330-959a-4827-b2ad-3425c0cdb4a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_stopped_budget_without_B_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_cash_witness_forces_B_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_generator_cells_L1_of_B_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ n, Integrable (fun ω =>
        let Z : ℕ → ℝ := fun i => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        (∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) *
                (X.generator w (Z i) - q * w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ))
            else 0)) P := by
  intro δ S n
  obtain ⟨M, B, Err, hBdef, hMint, hErrI, hErrT, hBudget⟩ :=
    avram_bv_residual9_original_stopped_budget_without_B_L1
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT u hgrid hmono
  have hMint' : ∀ m, Integrable (M m) P := fun m => (hMint m).1
  have hLem :=
    avram_bv_meas7_original_cash_witness_forces_B_L1
      X hX hBV q w hw_cont hw_neg C hw_gen hw_grad x D hD hw_nonneg
      T hT u hmono M Err hMint' hErrI (by simpa [hBdef] using hBudget)
  have hBint : ∀ m, Integrable (B m) P :=
    fun m => (hLem m).congr (Filter.Eventually.of_forall fun ω => (hBdef m ω).symm)
  let A : ℕ → Ω → ℕ → ℝ := fun m ω i =>
    if (u m i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u m i) ∧
        ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u m i)) < C then
      Real.exp (-(q * (u m i : ℝ))) *
        deriv w (Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u m i))
    else 0
  let G : ℕ → Ω → ℝ := fun m ω =>
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u m i)
    (∑ i ∈ Finset.range (m + 1),
      if (u m i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u m i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) *
          ((u m (i + 1) : ℝ) - (u m i : ℝ)) else 0)
  have hBeq : ∀ m ω,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
      B m ω = G m ω + ∑ i ∈ Finset.range (m + 1), A m ω i * (R (u m i) - R (u m (i + 1))) := by
    intro m ω J R
    have h := hBdef m ω
    simpa only [G, A] using h
  have hG : ∀ m, Integrable (G m) P ∧ B m =ᵐ[P] G m :=
    avram_bv_residual10_original_generator_cells_L1_of_B_L1
      X hX hBV u A B G hBeq hBint
  exact (hG n).1
