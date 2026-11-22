-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_positive_clock_physical_grid_pathwise_remainder_certificate_public_20261122
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:16:59.598825+00:00
-- url     : https://prove2.me/submissions/f25ceab8-19c8-4313-b618-ff9634ab5e6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

import Theorems.Thm_AvramDividend_Classical_avram_oai_original_positive_clock_cash_lastmesh_L1_auto_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_cofinal_event_L1_absolute_subsequence_of_eventual_bound_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_positive_clock_signed_ito_mesh_with_exact_cash_boundary_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω else riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) : ∀ k : ℕ,
      let A : Set Ω := {ω | σ k ω ≠ 0}
      ∃ (m : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0) (S : ℕ → ℕ → Set ℝ) (g : ℕ → ℕ → SimpleFunc ℝ ℝ) (H : ℕ → ℕ → Ω → ℝ) (K : ℕ → ℕ → ℝ) (E : ℕ → Ω → ℝ),
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        let B : ℕ → ℕ → ℝ → Set ℝ := fun j i y => S j i ∩ (g j i) ⁻¹' {y}
        let G : ℕ → ℕ → Ω → ℝ := fun j i ω => ∑ y ∈ (g j i).range, y * ((NX ω (Ioc (s j i) (t j i) ×ˢ B j i y)).toReal - ((((t j i - s j i : ℝ≥0) : ℝ≥0∞) * X.ν (B j i y))).toReal)
        let M : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range (m j), (if (σ k ω : WithTop ℝ≥0) ≤ (s j i : WithTop ℝ≥0) then 0 else H j i ω) * G j i ω
        (∀ j, ∀ i ∈ Finset.range (m j), s j i < t j i) ∧ (∀ j, ∀ i ∈ Finset.range (m j), MeasurableSet (S j i)) ∧ (∀ j, ∀ i ∈ Finset.range (m j), S j i ⊆ Iio (0 : ℝ)) ∧ (∀ j, ∀ i ∈ Finset.range (m j), X.ν (S j i) < ⊤) ∧
        (∀ j, ∀ i ∈ Finset.range (m j), StronglyMeasurable[𝓕.rightCont (s j i)] (H j i)) ∧
        (∀ j, ∀ i ∈ Finset.range (m j), ∀ ω, ‖H j i ω‖ ≤ K j i) ∧ (∀ j, ∀ i ∈ Finset.range (m j), ∀ ω, ω ∉ A → H j i ω = 0) ∧
        (∀ j, IntegrableOn (E j) A P) ∧ (∀ j, ∀ᵐ ω ∂(P.restrict A), F k ω ≤ w x + M j ω + E j ω) ∧
        Tendsto (fun j => ∫ ω in A, E j ω ∂P) atTop (𝓝 (0 : ℝ))  := by
  classical
  intro k A
  let CashRaw : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℝ≥0 := σ k ω - Δ
    q * (Δ : ℝ) * (dividendMeasure D ω (Ioo (0 : ℝ) (σ k ω : ℝ))).toReal + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioo (u : ℝ) (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  have hCashSmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → Integrable (CashRaw m) P ∧ (∫ ω, |CashRaw m ω| ∂P) ≤ ε := by
    simpa only [CashRaw] using (avram_oai_original_positive_clock_cash_lastmesh_L1_auto_20261122 X hX x C D hD q hq n hn τ hτeq σ hσstop hσle k)
  obtain ⟨r, hBI, hAbsEvent⟩ := avram_oai_cofinal_event_L1_absolute_subsequence_of_eventual_bound_20261122 P CashRaw hCashSmall
  let CashErr : ℕ → Ω → ℝ := fun j ω => CashRaw (r j) ω
  have hCashInt : ∀ j, IntegrableOn (CashErr j) A P := fun j => (hBI j).integrableOn
  have hCashAbs : Tendsto (fun j => ∫ ω in A, |CashErr j ω| ∂P) atTop (𝓝 (0 : ℝ)) := by
    simpa only [CashErr] using (hAbsEvent A).2
  have hCashSigned : Tendsto (fun j => ∫ ω in A, CashErr j ω ∂P) atTop (𝓝 (0 : ℝ)) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    have hNorm : ∀ j, ‖∫ ω in A, CashErr j ω ∂P‖ ≤ (∫ ω in A, |CashErr j ω| ∂P) := by
      intro j
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := P.restrict A) (CashErr j))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hCashAbs (fun j => norm_nonneg _) hNorm
  have hSource := avram_oai_original_positive_clock_signed_ito_mesh_with_exact_cash_boundary_20261122 X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop σ F hσstop hσle hFsource hFI hInfiniteActivity k r
  obtain ⟨m, s, t, S, g, H, K, R, hst, hS, hNeg, hνloc, hH, hBound, hSupp, hRI, hPath, hRlim⟩ := hSource
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let B : ℕ → ℕ → ℝ → Set ℝ := fun j i y => S j i ∩ (g j i) ⁻¹' {y}
  let G : ℕ → ℕ → Ω → ℝ := fun j i ω => ∑ y ∈ (g j i).range, y * ((NX ω (Ioc (s j i) (t j i) ×ˢ B j i y)).toReal - ((((t j i - s j i : ℝ≥0) : ℝ≥0∞) * X.ν (B j i y))).toReal)
  let M : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range (m j), (if (σ k ω : WithTop ℝ≥0) ≤ (s j i : WithTop ℝ≥0) then 0 else H j i ω) * G j i ω
  let E : ℕ → Ω → ℝ := fun j ω => R j ω + CashErr j ω
  have hEI : ∀ j, IntegrableOn (E j) A P := by
    intro j
    exact (hRI j).add (hCashInt j)
  have hELim : Tendsto (fun j => ∫ ω in A, E j ω ∂P) atTop (𝓝 (0 : ℝ)) := by
    have hEq : ∀ j, (∫ ω in A, E j ω ∂P) = (∫ ω in A, R j ω ∂P) + (∫ ω in A, CashErr j ω ∂P) := by
      intro j
      exact integral_add (hRI j) (hCashInt j)
    simp_rw [hEq]
    simpa only [add_zero] using hRlim.add hCashSigned
  have hPathE : ∀ j, ∀ᵐ ω ∂(P.restrict A), F k ω ≤ w x + M j ω + E j ω := by
    intro j
    filter_upwards [hPath j] with ω hω
    simpa only [E, CashErr, add_assoc] using hω
  exact ⟨m, s, t, S, g, H, K, E, hst, hS, hNeg, hνloc, hH, hBound, hSupp, hEI, hPathE, hELim⟩
