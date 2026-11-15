-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb75_original_linear_cross_covariance_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:07:19.426218+00:00
-- url     : https://prove2.me/submissions/d081453a-5fed-4527-b514-46cc9787e949

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB57_original_finitecap_linear_grid_cell_memLp_two
import Theorems.Thm_AvramDividend_Classical_avram_gb54_original_finitecap_linear_grid_diagonal_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_gb73_integral_L2_polarization
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) : ∀ k (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ σ k ω) (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → ∀ (j : ℕ),
      let L : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
        let H : ℕ → Ω → ℝ := fun i η => if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
        (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω)
      ∀ v : ℝ, Tendsto (fun m : ℕ => ∫ ω, (L m ω) ^ 2 ∂P) atTop (𝓝 v) →
        Tendsto (fun nm : ℕ × ℕ => ∫ ω, L nm.1 ω * L nm.2 ω ∂P) atTop (𝓝 v) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j L v hv
  let a : ℕ → ℝ := fun m => ∫ ω, (L m ω)^2 ∂P
  let d : ℕ × ℕ → ℝ := fun nm =>
    ∫ ω, (L nm.1 ω - L nm.2 ω)^2 ∂P
  let b : ℕ × ℕ → ℝ := fun nm =>
    ∫ ω, L nm.1 ω * L nm.2 ω ∂P
  change Tendsto b atTop (𝓝 v)
  have hLp (m : ℕ) : MemLp (L m) 2 P := by
    dsimp only [L]
    apply memLp_finset_sum (Finset.range (m + 1))
    intro i hi
    simpa using (avram_gbB57_original_finitecap_linear_grid_cell_memLp_two
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j m i hi)
  have hEnergy : Tendsto d atTop (𝓝 (0 : ℝ)) := by
    simpa only [d, L] using
      (avram_gb54_original_finitecap_linear_grid_diagonal_L2_cauchy
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j)
  have hFst : Tendsto Prod.fst (atTop : Filter (ℕ × ℕ)) (atTop : Filter ℕ) := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_fst (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have hSnd : Tendsto Prod.snd (atTop : Filter (ℕ × ℕ)) (atTop : Filter ℕ) := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_snd (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have ha : Tendsto a atTop (𝓝 v) := by simpa only [a] using hv
  have hNum : Tendsto (fun nm : ℕ × ℕ => a nm.1 + a nm.2 - d nm)
      atTop (𝓝 ((v + v) - 0)) := (ha.comp hFst).add (ha.comp hSnd) |>.sub hEnergy
  have hHalf : Tendsto (fun nm : ℕ × ℕ => (a nm.1 + a nm.2 - d nm) / 2)
      atTop (𝓝 v) := by
    convert hNum.div_const 2 using 1 <;> ring
  have hpol (m l : ℕ) : d (m,l) = a m + a l - 2 * b (m,l) := by
    exact (avram_gb73_integral_L2_polarization P (L m) (L l)
      ((hLp m).integrable_sq) ((hLp l).integrable_sq)
      ((hLp m).integrable_mul (hLp l)))
  have hEq (nm : ℕ × ℕ) :
      b nm = (a nm.1 + a nm.2 - d nm) / 2 := by
    have h := hpol nm.1 nm.2
    dsimp only [a, b, d] at *
    linarith
  convert hHalf using 1
  funext nm
  exact hEq nm
