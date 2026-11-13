-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva43_original_BV_physical_signed_two_error_mesh_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:20:49.520213+00:00
-- url     : https://prove2.me/submissions/52f62df6-d7d7-4300-bed2-8d9ba4e1382c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva57_original_BV_physical_joint_cell_contact_L1_signed_grid
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
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
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∃ N ErrCell ErrContact : ℕ → Ω → ℝ,
      (∀ m, Integrable (N m) P ∧ (∫ ω, N m ω ∂P) ≤ 0) ∧
      (∀ m, Integrable (fun ω => max (ErrCell m ω) 0) P) ∧
      (∀ m, Integrable (fun ω => max (ErrContact m ω) 0) P) ∧
      (∀ m, ∀ᵐ ω ∂P, F m ω ≤ w x + N m ω +
        max (ErrCell m ω) 0 + max (ErrContact m ω) 0) ∧
      Tendsto (fun m => ∫ ω, max (ErrCell m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun m => ∫ ω, max (ErrContact m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  intro δ S F
  obtain ⟨N, ErrCell, ErrContact, hN, hCellI, hContactI,
      hPath, hJoint⟩ :=
    avram_bva57_original_BV_physical_joint_cell_contact_L1_signed_grid
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hInfinite
  have hAdd : ∀ m : ℕ,
      (∫ ω, max (ErrCell m ω) 0 + max (ErrContact m ω) 0 ∂P) =
      (∫ ω, max (ErrCell m ω) 0 ∂P) +
      (∫ ω, max (ErrContact m ω) 0 ∂P) := by
    intro m
    simpa only [Pi.add_apply] using (integral_add' (hCellI m) (hContactI m))
  have hCellNonneg : ∀ m : ℕ,
      0 ≤ (∫ ω, max (ErrCell m ω) 0 ∂P) := by
    intro m
    exact integral_nonneg (fun ω => le_max_right _ _)
  have hContactNonneg : ∀ m : ℕ,
      0 ≤ (∫ ω, max (ErrContact m ω) 0 ∂P) := by
    intro m
    exact integral_nonneg (fun ω => le_max_right _ _)
  have hCellUpper : ∀ m : ℕ,
      (∫ ω, max (ErrCell m ω) 0 ∂P) ≤
      (∫ ω, max (ErrCell m ω) 0 + max (ErrContact m ω) 0 ∂P) := by
    intro m
    rw [hAdd m]
    exact le_add_of_nonneg_right (hContactNonneg m)
  have hContactUpper : ∀ m : ℕ,
      (∫ ω, max (ErrContact m ω) 0 ∂P) ≤
      (∫ ω, max (ErrCell m ω) 0 + max (ErrContact m ω) 0 ∂P) := by
    intro m
    rw [hAdd m]
    linarith [hCellNonneg m]
  exact ⟨N, ErrCell, ErrContact, hN, hCellI, hContactI,
    hPath,
    squeeze_zero hCellNonneg hCellUpper hJoint,
    squeeze_zero hContactNonneg hContactUpper hJoint⟩
