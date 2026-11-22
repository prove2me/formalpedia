-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_full_laplace_from_finite_simple_mark_formula
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:21:02.151852+00:00
-- url     : https://prove2.me/submissions/6060bdc3-09b3-4806-90ec-0d58cdc4ac16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/- Original a77 full physical negative-jump Laplace: substantive
   reduction to original-source simultaneous Borel marked-step convergence.
   Proven finite-support tsum identity and bounded exponential DCT furnish
   the deterministic and stochastic end steps. No false independence. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_finite_horizon_jump_series_is_source_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_negative_Borel_step_approximants
import Theorems.Thm_AvramDividend_Classical_avram_a77_nonpositive_exponential_expectation_dct

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hJoint : ∀ (n : ℕ) (B : Fin n → Set ℝ),
      (∀ i, MeasurableSet (B i)) →
      (∀ i, B i ⊆ Iio (0 : ℝ)) →
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      iIndepFun (fun i : Fin n => fun ω : Ω =>
        NX ω (Ioc 0 t ×ˢ B i)) P)
    (hCountLaw : ∀ (B : Set ℝ), MeasurableSet B →
      B ⊆ Iio (0 : ℝ) →
      (let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 t ×ˢ B)
       ∃ (K : Ω → ℕ) (r : ℝ≥0),
         Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
         (∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal) ∧
         (r : ℝ) = ((t : ℝ≥0∞) * X.ν B).toReal))
    (hSimple : ∀ (n : ℕ) (B : Fin n → Set ℝ),
      (∀ i, MeasurableSet (B i)) →
      (∀ i, B i ⊆ Iio (0 : ℝ)) →
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
      ∀ (a : Fin n → ℝ),
      (∫ ω, Real.exp (∑ i : Fin n,
        a i *
          (((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc 0 t ×ˢ B i)).toReal) ∂P) =
      Real.exp (∑ i : Fin n,
        (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
          (Real.exp (a i) - 1))) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hSupport :=
    avram_a77_original_finite_horizon_jump_series_is_source_finite_sum
      X hFinite t J hJEq
  obtain ⟨f, r, hfMeas, hfNonpos, hfLimit, hrLimit, hRep⟩ :=
    avram_a77_original_negative_Borel_step_approximants
      X hFinite t θ hθ J hJMeas hJEq hSupport hCountLaw
  have hMean : ∀ n : ℕ,
      (∫ ω, Real.exp (f n ω) ∂P) = Real.exp (r n) := by
    intro n
    obtain ⟨k, B, a, hMeas, hNeg, hPair, hAE, hr⟩ := hRep n
    calc
      (∫ ω, Real.exp (f n ω) ∂P) =
          (∫ ω, Real.exp (∑ i : Fin k, a i *
            (((Measure.count.restrict {u : ℝ≥0 |
              0 < u ∧ X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc 0 t ×ˢ B i)).toReal) ∂P) := by
        apply integral_congr_ae
        filter_upwards [hAE] with ω hω
        exact congrArg Real.exp hω
      _ = Real.exp (∑ i : Fin k,
          (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
            (Real.exp (a i) - 1)) := hSimple k B hMeas hNeg hPair a
      _ = Real.exp (r n) := by rw [hr]
  have hExpMean :
      Tendsto (fun n => Real.exp (r n)) atTop
        (𝓝 (∫ ω, Real.exp (θ * J ω) ∂P)) := by
    have hdct :=
      avram_a77_nonpositive_exponential_expectation_dct
        P f (fun ω => θ * J ω) hfMeas hfLimit hfNonpos
    simpa only [hMean] using hdct
  have hExpRate :
      Tendsto (fun n => Real.exp (r n)) atTop
        (𝓝 (Real.exp ((t : ℝ) *
          (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν)))) := by
    exact (Real.continuous_exp.tendsto _).comp hrLimit
  exact tendsto_nhds_unique hExpMean hExpRate

