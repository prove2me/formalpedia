-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb20_original_finitecap_postpaid_grid_L1_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:33:54.858832+00:00
-- url     : https://prove2.me/submissions/0b0fda56-ea19-498f-80da-9baf3716cb08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gb23_original_finitecap_postpaid_linear_grid_L1_limit
import Theorems.Thm_AvramDividend_Classical_avram_gb24_original_finitecap_quadratic_grid_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_gb27_original_finitecap_quadratic_grid_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ)
(hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧
ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x
: ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump
: ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω →
ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0)
(hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) : ∀ k (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle
: ∀ ω, ρ ω ≤ σ k ω) (δ : ℝ) (hδ : 0 < δ) (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω) (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → ∀ (j : ℕ),
    let M : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
      let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
      let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
      let H : ℕ → Ω → ℝ := fun i η => if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
      (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω + H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      ∃ (N: Ω → ℝ), Integrable N P ∧ (∫ ω in A, N ω ∂P) = 0 ∧ Tendsto (fun m : ℕ => ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA j
  let M : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
    let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
    let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
    let H : ℕ → Ω → ℝ := fun i η => if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
    (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω + H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
  let L : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
    let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
    let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
    let H : ℕ → Ω → ℝ := fun i η => if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
    (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω)
  let Q : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
    let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
    let G : ℕ → Ω → ℝ := fun i η => if s i < ρ η then Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then deriv w (Y i η) else 1) else 0
    let H : ℕ → Ω → ℝ := fun i η => if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) * (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0) else 0
    (Finset.range (m + 1)).sum (fun i => H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
  obtain ⟨N, hNI, hN0, hLN⟩ :=
    avram_gb23_original_finitecap_postpaid_linear_grid_L1_limit
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j
  have hLConv :
      Tendsto (fun m : ℕ => ∫ ω in A, |N ω - L m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    simpa [L] using hLN
  have hQConv :
      Tendsto (fun m : ℕ => ∫ ω in A, |Q m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    simpa [Q] using
      (avram_gb24_original_finitecap_quadratic_grid_L1_vanish
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j)
  have hMeq (m : ℕ) (ω : Ω) :
      M m ω = L m ω + Q m ω := by
    simp only [M, L, Q, Finset.sum_add_distrib]
  have hMInt (m : ℕ) : IntegrableOn (M m) A P := by
    obtain ⟨hI, _⟩ :=
      avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle
        δ hδ hFloor A hA (fun _ => m)
    simpa [M] using hI j
  have hQInt (m : ℕ) : IntegrableOn (Q m) A P := by
    simpa [Q] using
      (avram_gb27_original_finitecap_quadratic_grid_integrable
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle k ρ hρstop hρle δ hδ hFloor A hA j m)
  have hLInt (m : ℕ) : IntegrableOn (L m) A P := by
    have h := (hMInt m).sub (hQInt m)
    convert h using 1
    funext ω
    change L m ω = M m ω - Q m ω
    linarith [hMeq m ω]
  have hUpper (m : ℕ) :
      (∫ ω in A, |N ω - M m ω| ∂P) ≤
      (∫ ω in A, |N ω - L m ω| ∂P) +
        (∫ ω in A, |Q m ω| ∂P) := by
    have hMAbs :
        IntegrableOn (fun ω => |N ω - M m ω|) A P :=
      ((hNI.integrableOn).sub (hMInt m)).abs
    have hLAbs :
        IntegrableOn (fun ω => |N ω - L m ω|) A P :=
      ((hNI.integrableOn).sub (hLInt m)).abs
    have hQAbs :
        IntegrableOn (fun ω => |Q m ω|) A P := (hQInt m).abs
    have hAlmost : ∀ᵐ ω ∂(P.restrict A),
        |N ω - M m ω| ≤ |N ω - L m ω| + |Q m ω| := by
      filter_upwards [] with ω
      rw [hMeq m ω]
      calc
        |N ω - (L m ω + Q m ω)| =
            |(N ω - L m ω) - Q m ω| := by congr 1; ring
        _ ≤ |N ω - L m ω| + |Q m ω| := by
          simpa using (abs_sub_le (N ω - L m ω) 0 (Q m ω))
    calc
      _ ≤ ∫ ω in A, |N ω - L m ω| + |Q m ω| ∂P :=
        integral_mono_ae hMAbs (hLAbs.add hQAbs) hAlmost
      _ = _ := by
        simpa only [Pi.add_apply] using (integral_add hLAbs hQAbs)
  have hNonneg (m : ℕ) :
      0 ≤ ∫ ω in A, |N ω - M m ω| ∂P :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hSum : Tendsto
      (fun m : ℕ => (∫ ω in A, |N ω - L m ω| ∂P) +
        (∫ ω in A, |Q m ω| ∂P)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using hLConv.add hQConv
  refine ⟨N, hNI, hN0, ?_⟩
  apply Filter.Tendsto.squeeze (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hSum
  · exact hNonneg
  · exact hUpper
