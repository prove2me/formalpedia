-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_finitecap_boundedstop_joint_intrinsic_gaussian_fullmark_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:37:14.935199+00:00
-- url     : https://prove2.me/submissions/54b9e92c-ebf6-44d5-8396-08e8912b6966

/-
  The original clipped Gaussian residual and full negative-mark compensated
  integral are jointly centred at the same bounded stopping time.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finitecap_fullnegative_stopped_compensator_initial_centered
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
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
    (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0)
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
      Integrable (fun ω => R (σ ω) ω) P ∧
      Integrable J P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, R (σ ω) ω ∂P) = 0 ∧
        (∫ ω in A, J ω ∂P) = 0)
:= by
  obtain ⟨R, Jsmall, hRcont, hRlim, hSmallLim, hRI, hSmallI, hRcenter⟩ :=
    avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
      X hX hFiniteActivity n hn σ hσstop hσbound
  have hJcenter :=
    avram_freshD_original_finitecap_fullnegative_stopped_compensator_initial_centered
      X x q hq C hFiniteCap w hw_cont hw_neg D hD
      n σ hσstop hσbound hFiniteActivity
  refine ⟨R, hRlim, hRI, hJcenter.1, ?_⟩
  intro A hA
  exact ⟨(hRcenter A hA).1, hJcenter.2 A hA⟩
