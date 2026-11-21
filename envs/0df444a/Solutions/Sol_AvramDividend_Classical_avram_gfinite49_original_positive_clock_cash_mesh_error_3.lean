-- Prove2me | solution 3 for AvramDividend.Classical.avram_gfinite49_original_positive_clock_cash_mesh_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:02:28.519249+00:00
-- url     : https://prove2.me/submissions/11024c9b-2db2-48c4-abd3-8c6371898b68
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gfinite48_original_fixed_band_cash_error
import Theorems.Thm_AvramDividend_Classical_avram_gfinite49_cofinal_positive_error_diagonal
import Theorems.Thm_AvramDividend_Classical_avram_gfinite56_cap_fraction_cutoff_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
  SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q :
  ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (hw0 : 0 ≤ w 0)
  (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y
  : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
  X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y →
  ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0
  → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime
  X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime
  X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω -
  (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min
  (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop :
  IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0) (hσstop : ∀ k,
  IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) : ∀ k
  (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω,
  ρ ω ≤ σ k ω) (δ : ℝ) (hδ : 0 < δ) (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x
  D t ω) (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → ∃ (N : ℕ → ℕ),
        let Δ : ℕ → ℝ≥0 := fun j => (n : ℝ≥0) / ((N j + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
        let a : ℝ := δ / 2; let b : ℕ → ℝ := fun j =>
          C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → ℕ → Ω → ℝ := fun j i ω => x + X.X (s j i) ω - rightLimit D (s j i) ω
        let Z : ℕ → ℕ → Ω → ℝ := fun j i ω => X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
        let G : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then Real.exp (-(q * (s j i : ℝ))) *
            (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω) else 1) else 0
        let H : ℕ → ℕ → Ω → ℝ := fun j i ω => if s j i < ρ ω then (1 / 2 : ℝ) *
            Real.exp (-(q * (s j i : ℝ))) * (if Y j i ω ∈ Icc a (b j)
             then iteratedDeriv 2 w (Y j i ω) else 0) else 0
        let M : ℕ → Ω → ℝ := fun j ω => (Finset.range (N j + 1)).sum (fun i =>
            G j i ω * Z j i ω + H j i ω * (Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2))
        let F : Ω → ℝ := fun ω => if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
        StrictMono N ∧ ∃ (E : ℕ → Ω → ℝ), (∀ j, IntegrableOn (E j) A P) ∧
          Tendsto (fun j => ∫ ω in A, max (E j ω) 0 ∂P)
            atTop (𝓝 (0 : ℝ)) ∧ (∀ j, ∀ᵐ ω ∂(P.restrict A),
            ρ ω ≠ 0 → F ω ≤ w x + M j ω + E j ω) ∧
          (∀ j ω, ρ ω = 0 → E j ω = 0) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA
  let F : Ω → ℝ := fun ω => if ρ ω = 0 then w x else
    Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
    (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
    ENNReal.ofReal (Real.exp (-(q * z))) ∂(dividendMeasure D ω)).toReal
  let M2 : ℕ → ℕ → Ω → ℝ := fun j m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    let G : ℕ → Ω → ℝ := fun i ω => if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) * (if Y i ω ∈ Icc a b then deriv w (Y i ω) else 1) else 0
    let H : ℕ → Ω → ℝ := fun i ω => if s i < ρ ω then
      (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
      (if Y i ω ∈ Icc a b then iteratedDeriv 2 w (Y i ω) else 0) else 0
    (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω +
      H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
  let b : ℕ → ℝ := fun j => C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let θ : ℕ → ℝ := fun j => (w C.toReal - w (b j)) - (C.toReal - b j)
  let eps : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hCpos : 0 < C.toReal := ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hTheta : Tendsto θ atTop (𝓝 (0 : ℝ)) :=
    avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero w C.toReal hCpos hw_cont b
      (avram_gfinite56_cap_fraction_cutoff_tendsto C.toReal)
  have hEps : Tendsto eps atTop (𝓝 (0 : ℝ)) := by exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hLocal : ∀ j K : ℕ, ∃ m : ℕ, K < m ∧ ∃ E : Ω → ℝ,
    IntegrableOn E A P ∧ (∀ᵐ ω ∂(P.restrict A), F ω ≤ w x + M2 j m ω + E ω) ∧
    (∫ ω in A, max (E ω) 0 ∂P) ≤ θ j + eps j := by
    intro j K; obtain ⟨m, hm, E, hEI, hUpper, hMean⟩ :=
      AvramDividend.Classical.avram_gfinite48_original_fixed_band_cash_error
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop σ hσstop hσle
        k ρ hρstop hρle δ hδ hFloor A hA j (eps j) (by
          dsimp [eps]; positivity) K
    exact ⟨m, hm, E, hEI, hUpper, hMean⟩
  obtain ⟨N, hN, E, hEI, hVan, hUpper⟩ :=
    AvramDividend.Classical.avram_gfinite49_cofinal_positive_error_diagonal
      P A F (w x) M2 θ eps hTheta hEps hLocal
  have hS : MeasurableSet {ω : Ω | ρ ω ≠ 0} := ((𝓕.rightCont).le 0) _
    (avram_ubv_finite12_positive_clock_initial_measurable ρ hρstop)
  let E' : ℕ → Ω → ℝ := fun j ω => if ρ ω = 0 then 0 else E j ω
  have hI' : ∀ j, IntegrableOn (E' j) A P := by
    intro j
    have heq : E' j = {ω : Ω | ρ ω ≠ 0}.indicator (E j) := by
      funext ω; by_cases hz : ρ ω = 0 <;> simp [E', hz, Set.indicator]
    rw [heq]; exact (hEI j).indicator hS
  have hM : ∀ j, (∫ ω in A, max (E' j ω) 0 ∂P) ≤
    (∫ ω in A, max (E j ω) 0 ∂P) := by
    intro j; apply integral_mono_ae ((hI' j).pos_part) ((hEI j).pos_part)
    filter_upwards [] with ω; by_cases hz : ρ ω = 0
    · simpa [E', hz] using (le_max_right (E j ω) 0)
    · simp [E', hz]
  have hVan' := squeeze_zero (fun j => integral_nonneg
    (fun ω => le_max_right (E' j ω) 0)) hM hVan
  refine ⟨N, hN, E', hI', hVan', ?_, ?_⟩
  · intro j; filter_upwards [hUpper j] with ω hw; intro hnz
    simpa [E', hnz, F, M2] using hw
  · intro j ω hz; simp [E', hz]
