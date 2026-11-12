-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB115_original_finitecap_two_mesh_refinement_energy_tendsto_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:23:03.559579+00:00
-- url     : https://prove2.me/submissions/fbad1541-fca9-4438-a778-1241903f7b3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB116_original_finitecap_one_mesh_gradient_L2_to_physical_limit
import Theorems.Thm_AvramDividend_Classical_avram_gbB121_original_finitecap_two_mesh_energy_triangle_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB82_original_two_mesh_time_energy_grid_exact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ (j : ℕ),
      let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℝ := x + X.X s ω - rightLimit D s ω
        if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
          (if Y ∈ Icc a b then deriv w Y else 1)
        else 0
      let E : ℕ × ℕ → ℝ := fun nm =>
        let m : ℕ := nm.1
        let p : ℕ := nm.2
        let N : ℕ := (m + 1) * (p + 1)
        let Δ : ℝ := (n : ℝ) / (N : ℝ)
        Δ * (Finset.range N).sum (fun i =>
          ∫ ω, (G m (i / (p + 1)) ω -
            G p (i / (m + 1)) ω) ^ 2 ∂P)
      let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        (Finset.range (m + 1)).sum (fun i =>
          if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
          then G m i ω else 0)
      Tendsto E atTop (𝓝 (0 : ℝ)) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j
  have hV :=
    avram_gbB116_original_finitecap_one_mesh_gradient_L2_to_physical_limit
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j
  have hBound :=
    avram_gbB121_original_finitecap_two_mesh_energy_triangle_bound
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j
  have hEq :=
    avram_gbB82_original_two_mesh_time_energy_grid_exact
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j
  have hFst : Tendsto Prod.fst
      (atTop : Filter (ℕ × ℕ)) (atTop : Filter ℕ) := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_fst (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have hSnd : Tendsto Prod.snd
      (atTop : Filter (ℕ × ℕ)) (atTop : Filter ℕ) := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_snd (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have hUpper := ((hV.comp hFst).add (hV.comp hSnd)).const_mul (2 : ℝ)
  simp only [add_zero, mul_zero] at hUpper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun _ : ℕ × ℕ => (0 : ℝ)) atTop
      (𝓝 (0 : ℝ)) from tendsto_const_nhds) hUpper ?_ ?_
  · intro nm
    rw [hEq nm.1 nm.2]
    exact integral_nonneg (fun t =>
      integral_nonneg (fun ω => sq_nonneg _))
  · intro nm
    exact hBound nm.1 nm.2
