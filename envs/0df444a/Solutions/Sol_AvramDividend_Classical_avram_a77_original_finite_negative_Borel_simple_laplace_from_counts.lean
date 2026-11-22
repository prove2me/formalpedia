-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_finite_negative_Borel_simple_laplace_from_counts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:42:11.970268+00:00
-- url     : https://prove2.me/submissions/87a0c1bc-67a7-476d-8f5d-9e68f8a85d46

/- Original source finite disjoint Borel mark Laplace: use the
   actual physical independent Nat count representatives (Open source
   transfer obligation) and Proved/active general finite Poisson PGF.
   No synthetic Gaussian or independent-jump process is introduced. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_spatial_poisson_Nat_count_family_realisation
import Theorems.Thm_AvramDividend_Classical_avram_a77_finite_independent_poisson_exp_product

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0)
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
    (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (a : Fin n → ℝ) :
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
          (Real.exp (a i) - 1)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  obtain ⟨K, r, hK, hIndep, hLaw, hEq, hRate⟩ :=
    avram_a77_original_spatial_poisson_Nat_count_family_realisation
      X hFinite t hJoint hCountLaw n B hMeas hNeg hPair
  have hProduct := avram_a77_finite_independent_poisson_exp_product
    P n K hK hIndep r hLaw a
  have hAE :
      (fun ω : Ω => Real.exp (∑ i : Fin n,
        a i * (NX ω (Ioc 0 t ×ˢ B i)).toReal)) =ᵐ[P]
      (fun ω : Ω => ∏ i : Fin n, Real.exp (a i) ^ K i ω) := by
    filter_upwards [hEq] with ω hω
    have hSum : (∑ i : Fin n,
        a i * (NX ω (Ioc 0 t ×ˢ B i)).toReal) =
        ∑ i : Fin n, a i * (K i ω : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hω i]
    rw [hSum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  change (∫ ω, Real.exp (∑ i : Fin n,
      a i * (NX ω (Ioc 0 t ×ˢ B i)).toReal) ∂P) =
      Real.exp (∑ i : Fin n,
        (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
          (Real.exp (a i) - 1))
  calc
    (∫ ω, Real.exp (∑ i : Fin n,
        a i * (NX ω (Ioc 0 t ×ˢ B i)).toReal) ∂P) =
        (∫ ω, ∏ i : Fin n, Real.exp (a i) ^ K i ω ∂P) :=
      integral_congr_ae hAE
    _ = ∏ i : Fin n, Real.exp
        ((r i : ℝ) * (Real.exp (a i) - 1)) := hProduct
    _ = Real.exp (∑ i : Fin n,
        (r i : ℝ) * (Real.exp (a i) - 1)) := by
      rw [Real.exp_sum]
    _ = Real.exp (∑ i : Fin n,
        (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
          (Real.exp (a i) - 1)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hRate i]
