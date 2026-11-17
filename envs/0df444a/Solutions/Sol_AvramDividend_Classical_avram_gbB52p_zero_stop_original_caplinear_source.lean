-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB52p_zero_stop_original_caplinear_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:15:32.81395+00:00
-- url     : https://prove2.me/submissions/b1475f32-ecde-40fb-a3d1-c52811bd71e2

import Theorems.Thm_AvramDividend_Classical_avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_gbB78_original_zero_stop_all_physical_gaussian_Hermite_source_and_cash_exact_zero
import Theorems.Thm_AvramDividend_Classical_avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_gbB54zz_event_restricted_zero_L1_limit_ae
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X
: SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (hc
: 0 < X.c) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (hw0 :
0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn
ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y →
ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0
→ Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime
X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime
X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω -
(rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min
(ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop :
IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0) (hσstop : ∀ k,
IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ (j : ℕ),
      let M : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η =>
          x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η =>
          X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        (Finset.range (m + 1)).sum (fun i =>
          G i ω * Z i ω + H i ω *
            (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      ∀ (N : Ω → ℝ), Integrable N P →
        Tendsto (fun m : ℕ =>
          ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ)) →
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let F : Ω → ℝ := fun ω =>
          if ρ ω = 0 then w x else
            Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * z)))
              ∂(dividendMeasure D ω)).toReal
        let Occ : Ω → ℝ := fun ω =>
          ∫ t in Ioo (0 : ℝ) (n : ℝ),
            if t < (ρ ω : ℝ) ∧
                b < riskProcess X x D (Real.toNNReal t) ω
            then (1 : ℝ) else 0 ∂volume
        ∀ᵐ ω ∂(P.restrict A),
          ρ ω = 0 →
          F ω - w x ≤ N ω +
            ((w C.toReal - w b) - (C.toReal - b)) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA j M N hNI hLimit b F Occ
  let μ : Measure Ω := P.restrict A
  let B : Set Ω := {ω | ρ ω = 0}
  have hB : MeasurableSet B := by
    have ht : MeasurableSet[𝓕.rightCont 0]
        {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ 0} := hρstop 0
    have heq : {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ 0} = B :=
      Set.ext (fun ω => by simp only [B, Set.mem_setOf_eq, WithTop.coe_le_coe, nonpos_iff_eq_zero, WithTop.coe_eq_zero])
    rw [heq] at ht
    exact MeasureTheory.measurableSet_of_filtration ht
  have hMInt (m : ℕ) : Integrable (M m) μ := by
    let Q : ℕ → ℕ := fun _ => m
    have h := (avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA Q).1 j
    simpa only [M, Q, μ] using h.integrable
  have hMZero (m : ℕ) (ω : Ω) (hz : ω ∈ B) : M m ω = 0 := by
    simpa only [M] using (avram_gbB78_original_zero_stop_all_physical_gaussian_Hermite_source_and_cash_exact_zero
      X q x w C D ρ δ j n m ω hz).2
  have hNZero : ∀ᵐ ω ∂μ, ω ∈ B → N ω = 0 :=
    avram_gbB54zz_event_restricted_zero_L1_limit_ae μ B hB N M (hNI.mono_measure Measure.restrict_le_self) hMInt hMZero hLimit
  have hCorner : 0 ≤ (w C.toReal - w b) - (C.toReal - b) := by
    simpa only [b] using (avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
      C hC hFiniteCap w hw_cont hw_smooth hw_grad j).2.2
  filter_upwards [hNZero] with ω hω; intro hρ
  have hF : F ω = w x := by
    simpa only [F] using (avram_gbB78_original_zero_stop_all_physical_gaussian_Hermite_source_and_cash_exact_zero
      X q x w C D ρ δ j n 0 ω hρ).1
  rw [hF, hω hρ]
  simpa only [sub_self, zero_add] using hCorner
