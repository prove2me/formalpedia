-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_negative_Borel_step_approximants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:33:14.988456+00:00
-- url     : https://prove2.me/submissions/1215af9e-d72a-466b-849c-59dccecc8685

/- The actual original physical marked finite Borel quantisation
   is a source-specific Open obligation; the negative Levy intensity
   DCT is a separate directly proved finite-measure consequence. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_finite_Borel_mark_exponent_quantizers
import Theorems.Thm_AvramDividend_Classical_avram_a77_finite_negative_measure_exp_deficit_dct
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
    (hSupport :
      ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
        J ω = ∑ u ∈ S,
          (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u))
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
    :
    ∃ (f : ℕ → Ω → ℝ) (r : ℕ → ℝ),
      (∀ n, Measurable (f n)) ∧
      (∀ᵐ ω ∂P, ∀ n, f n ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (θ * J ω))) ∧
      Tendsto r atTop (𝓝 ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν))) ∧
      ∀ n : ℕ, ∃ (k : ℕ) (B : Fin k → Set ℝ) (a : Fin k → ℝ),
        (∀ i, MeasurableSet (B i)) ∧
        (∀ i, B i ⊆ Iio (0 : ℝ)) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
        (∀ᵐ ω ∂P, f n ω =
          ∑ i : Fin k, a i *
            (((Measure.count.restrict {u : ℝ≥0 |
                0 < u ∧ X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B i)).toReal) ∧
        r n = ∑ i : Fin k,
          (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
            (Real.exp (a i) - 1) := by
  obtain ⟨q, f, r, hqMeas, hqNonpos, hqLimit,
    hfMeas, hfNonpos, hfLimit, hRate, hStep⟩ :=
    avram_a77_original_finite_Borel_mark_exponent_quantizers
      X hFinite t θ hθ J hJMeas hJEq hSupport hCountLaw
  have hDCT := avram_a77_finite_negative_measure_exp_deficit_dct
    X.ν hFinite θ q hqMeas hqNonpos hqLimit
  have hRateLimit :
      Tendsto r atTop (𝓝 ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν))) := by
    have hr : r = fun n => (t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (q n y) - 1 ∂X.ν) :=
      funext hRate
    rw [hr]
    exact tendsto_const_nhds.mul hDCT
  exact ⟨f, r, hfMeas, hfNonpos, hfLimit, hRateLimit, hStep⟩

