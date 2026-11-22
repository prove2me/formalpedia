-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_laplace_from_joint_negative_Borel_Poisson_counts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:35:39.669925+00:00
-- url     : https://prove2.me/submissions/277fc37e-6da4-4487-96b5-4c3d391531e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/- Original 8bb source-specific Poisson marked jump Laplace.
   Accepted a77 parent imports 8bb; this sketch separates genuine finite
   Borel-weighted count exponential product from final finite-negative-
   activity approximation to the original physical signed jump sum. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_finite_negative_Borel_simple_laplace_from_counts
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_full_laplace_from_finite_simple_mark_formula

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
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
         (r : ℝ) = ((t : ℝ≥0∞) * X.ν B).toReal)) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by
  exact avram_a77_original_full_laplace_from_finite_simple_mark_formula
    X hFinite t θ hθ J hJMeas hJEq hJoint hCountLaw
    (fun n B hMeas hNeg hPair a =>
      avram_a77_original_finite_negative_Borel_simple_laplace_from_counts
        X hFinite t hJoint hCountLaw n B hMeas hNeg hPair a)
