-- Prove2me | solution 1 for AvramDividend.Classical.avram_jp20261122_finitecap_positive_clock_true_physical_fullmark_ito_mesh_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:18:14.322802+00:00
-- url     : https://prove2.me/submissions/544ffee7-a4b9-49f3-ad0b-5433f4a2ed58
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_jp20261122_original_ruinclipped_positive_clock_exact_finite_ito_source_ledger
import Theorems.Thm_AvramDividend_Classical_avram_jp20261122_finitecap_positive_true_physical_explicit_mesh_residual_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν :
    X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y
    - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD :
    IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t :
    ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (σ :
    Ω → ℝ≥0) (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) (hσclip : ∀ ω, σ ω ≤ (min (ruinTime X x D ω) (n :
    ℝ≥0∞)).toNNReal) (F : Ω → ℝ) (hFsource : ∀ ω, F ω = Real.exp (-(q * (σ ω : ℝ))) * w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ ω) ω - rightLimit
    D (σ ω) ω else riskProcess X x D (σ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D
    ω)).toReal) (hFI : Integrable F P) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hFiniteCap : C ≠ ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map (fun t : ℝ≥0 => (t, X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω)
      t)))
    let μT : Measure ℝ≥0 := ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧ (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧ 0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then Real.exp (-(q * (p.1.1 : ℝ))) * (w (Y p.1 + p.2) - w (Y
      p.1)) else 0
    let J : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    ∀ (R : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun j : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
          atTop (𝓝 (R t ω))) →
      ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∀ ε : ℝ, 0 < ε →
      ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
        (WG : ℕ → Ω → ℝ) (L : ℝ)
        (G E : Ω → ℝ),
        (∀ i ∈ S, a i ≤ b i ∧ b i ≤ (n : ℝ≥0)) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧
        0 ≤ L ∧ (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ L) ∧
        (∀ ω, G ω = ∑ i ∈ S,
          (if σ ω ≤ a i then 0 else WG i ω) *
            (R (b i) ω - R (a i) ω)) ∧
        IntegrableOn G A P ∧ IntegrableOn E A P ∧
        (∀ ω, σ ω = 0 → 0 ≤ E ω) ∧
        (∀ᵐ ω ∂(P.restrict A),
          σ ω ≠ 0 → F ω ≤ w x + G ω + J ω + E ω) ∧
        IntegrableOn (fun ω =>
          max (F ω - w x - G ω - J ω) 0) A P ∧
        (∫ ω in A, |E ω| ∂P) ≤ ε := by
  classical
  intro Y NX μT H J R hR A hA ε hε
  let Mesh : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
      let V : ℕ → ℝ := fun i => x + X.X (v i) ω - rightLimit D (v i) ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let W : ℝ := if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ ω) ω - rightLimit D (σ ω) ω else riskProcess X x D (σ ω) ω
      let Cash : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      (∑ i ∈ Finset.range m, ((e (i + 1) * w (Z i) - e i * w (V i)) + e (i + 1) * (w (V (i +
        1)) - w (Z i)))) + (Real.exp (-(q * (σ ω : ℝ))) * w W - e m * w (V m)) + (e 0 * w (V 0) - w x) + Cash
  obtain ⟨m, S, a, b, WG, L, G,
      hS, hWG, hL, hBound, hGSource, hGI, hRI, hRBound⟩ :=
    avram_jp20261122_finitecap_positive_true_physical_explicit_mesh_residual_L1
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn σ hσstop hσbound hσclip F hFsource hFI
      hFiniteActivity hFiniteCap R hR A hA ε hε
  let E : Ω → ℝ := fun ω => max (Mesh m ω - G ω - J ω) 0
  have hLedger : ∀ ω, F ω - w x = Mesh m ω := by
    intro ω
    exact avram_jp20261122_original_ruinclipped_positive_clock_exact_finite_ito_source_ledger
      X x q w D hD.1.1 σ n F hFsource m ω
  have hEpos (ω : Ω) : 0 ≤ E ω := by exact le_max_right _ _
  have hMaxEq :
      (fun ω => max (F ω - w x - G ω - J ω) 0) = E := by
    funext ω
    change max (F ω - w x - G ω - J ω) 0 =
      max (Mesh m ω - G ω - J ω) 0
    rw [hLedger ω]
  have hPositive :
      ∀ᵐ ω ∂(P.restrict A),
        σ ω ≠ 0 → F ω ≤ w x + G ω + J ω + E ω := by
    filter_upwards [] with ω
    intro _
    have hh : Mesh m ω - G ω - J ω ≤ E ω := le_max_left _ _
    linarith [hLedger ω]
  refine ⟨S, a, b, WG, L, G, E,
    hS, hWG, hL, hBound, hGSource, hGI, hRI,
    (fun ω _ => hEpos ω), hPositive, ?_, ?_⟩
  · rw [hMaxEq]
    exact hRI
  · have hAbs : (fun ω => |E ω|) = E := by
      funext ω
      exact abs_of_nonneg (hEpos ω)
    rw [hAbs]
    exact hRBound
