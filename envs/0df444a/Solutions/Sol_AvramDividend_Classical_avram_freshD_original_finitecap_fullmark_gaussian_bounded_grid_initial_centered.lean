-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_finitecap_fullmark_gaussian_bounded_grid_initial_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:50:47.159347+00:00
-- url     : https://prove2.me/submissions/e78a622c-04a5-4cba-86d1-be4153e63fad

/-
  The exact original fullnegative marked compensator and every bounded
  predictable finite Gaussian grid gain are centred on initial events.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finitecap_fullnegative_stopped_compensator_initial_centered
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hFiniteCap : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t,
            X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    let J : Ω → ℝ := fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
            atTop (𝓝 (R t ω))) ∧
      Integrable J P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, J ω ∂P) = 0) ∧
      ∀ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
        (WG : ℕ → Ω → ℝ)
        (hab : ∀ i ∈ S, a i ≤ b i)
        (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
        (L : ℝ) (hL : 0 ≤ L)
        (hWGbound : ∀ i ∈ S, ∀ (ω : Ω), ‖WG i ω‖ ≤ L),
      let G : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)
      Integrable G P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, G ω ∂P) = 0)
:= by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, Jsmall, hRlim, hJsmalllim, hGrid⟩ :=
    avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
      X hX hFiniteActivity
  have hJcenter :=
    avram_freshD_original_finitecap_fullnegative_stopped_compensator_initial_centered
      X x q hq C hFiniteCap w hw_cont hw_neg D hD
      n σ hσstop hσbound hFiniteActivity
  refine ⟨R, hRlim, hJcenter.1, hJcenter.2, ?_⟩
  intro S a b WG hab hWG L hL hWGbound
  have hWJ : ∀ i ∈ S,
      Measurable[𝓕.rightCont (a i)] ((fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) i : Ω → ℝ) := by
    intro i hi
    exact measurable_const
  have hWJbound : ∀ i ∈ S, ∀ (ω : Ω),
      ‖((fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) i ω)‖ ≤ (0 : ℝ) := by
    simp
  have hBoth := hGrid S a b WG (fun (_ : ℕ) (_ : Ω) => (0 : ℝ))
    hab hWG hWJ σ hσstop L 0 hL le_rfl hWGbound hWJbound
  refine ⟨hBoth.1, ?_⟩
  intro A hA
  exact avram_ubv_jump11_past_event_integral_of_condexp_zero
    (𝓕.rightCont 0) (𝓕.rightCont.le 0)
    _ hBoth.1 hBoth.2.1 A hA
