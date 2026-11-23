-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_finite_Borel_mark_exponent_quantizers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:48:12.972952+00:00
-- url     : https://prove2.me/submissions/1771f59a-024a-419c-a973-8f7e314c0ae2

/- Original physical Avram negative Borel mark quantiser: reduce
   to directly provable nonpositive SimpleFunc approximation and genuine
   original count-fibre and finite-support reconstruction. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a77_nonpositive_negative_Borel_simpleFunc_approx
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_simpleFunc_physical_mark_count_reconstruction
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
    ∃ (q : ℕ → ℝ → ℝ) (f : ℕ → Ω → ℝ) (r : ℕ → ℝ),
      (∀ n, Measurable (q n)) ∧
      (∀ n y, y < 0 → q n y ≤ 0) ∧
      (∀ y, y < 0 → Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) ∧
      (∀ n, Measurable (f n)) ∧
      (∀ᵐ ω ∂P, ∀ n, f n ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (θ * J ω))) ∧
      (∀ n, r n = (t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (q n y) - 1 ∂X.ν)) ∧
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
  obtain ⟨q, hqNonpos, hqLimit⟩ :=
    avram_a77_nonpositive_negative_Borel_simpleFunc_approx θ hθ
  obtain ⟨f, r, hfMeas, hfNonpos, hfLimit, hRate, hStep⟩ :=
    avram_a77_original_simpleFunc_physical_mark_count_reconstruction
      X hFinite t θ hθ J hJMeas hJEq hSupport hCountLaw
      q hqNonpos hqLimit
  have hqNonposNeg : ∀ n y, y < 0 → (q n) y ≤ 0 :=
    fun n y _ => hqNonpos n y
  refine ⟨(fun n y => q n y), f, r, ?_, hqNonposNeg, hqLimit,
    hfMeas, hfNonpos, hfLimit, hRate, hStep⟩
  intro n
  exact (q n).measurable

