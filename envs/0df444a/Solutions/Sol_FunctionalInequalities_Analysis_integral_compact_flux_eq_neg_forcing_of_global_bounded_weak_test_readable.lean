-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:47.552061+00:00
-- url     : https://prove2.me/submissions/deb1e291-cce3-435d-be86-e2432ced48ce

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_compact_mul_data_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_flux_eq_neg_forcing_of_bounded_weak_test_readable

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section CompactFluxGlobalBoundedWeakTest
open MeasureTheory Filter Set Metric
open scoped ContDiff Topology RealInnerProductSpace
/-- Integration by parts of a compactly supported compact-local L2 flux `J` with locally integrable forcing `F`
(tested identity against compact C1 tests) against a globally bounded locally integrable weak function `η` whose
coordinate weak derivatives are L2 on compact sets: both pairings are integrable and `∫ ∑ Jᵢ aᵢ = -∫ F η`. -/
theorem solution {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hJ : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hJc : ∀ i : Fin n, HasCompactSupport (J i)) (hFc : HasCompactSupport F)
    (hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let S := tsupport F ∪ ⋃ i : Fin n, tsupport (J i)
  have hS : IsCompact S := hFc.union (isCompact_iUnion hJc)
  obtain ⟨R, hR, hRS⟩ := hS.isBounded.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨R, R + 1, hR, lt_add_one R⟩
  have hχ1 (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) : χ x = 1 :=
    χ.one_of_mem_closedBall (ball_subset_closedBall (hRS hx))
  have hχd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) (i : Fin n) :
      fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) = 0 := by
    have he := (χ.eventuallyEq_one_of_mem_ball (hRS hx)).fderiv_eq (𝕜 := ℝ)
    simpa using congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) he
  let b := fun i x => χ x * a i x +
    fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) * η x
  have htop : MemLp η (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound hη.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)
  have hdata (i : Fin n) := FunctionalInequalities.Analysis.HasWeakDerivAlong.compact_mul_data_readable
    (hweak i) (ha2 i) (fun T _ => htop.restrict T)
    (χ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) χ.hasCompactSupport
  have hηχ : LocallyIntegrable (fun x => χ x * η x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [mul_comm] using hη.continuous_mul χ.continuous
  have hbχ (x : EuclideanSpace ℝ (Fin n)) : ‖χ x * η x‖ ≤ C := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    exact (mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg _)).trans
      (by simpa only [one_mul] using hbound x)
  obtain ⟨hprod, hforce, hEq⟩ := FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test_readable
    hJ hF hId hηχ hbχ χ.hasCompactSupport.mul_right
    (fun i => (hdata i).1) (fun i => (hdata i).2.2.1) (fun i => (hdata i).2.2.2)
  have hJeq (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      J i x * b i x = J i x * a i x := by
    by_cases hx : J i x = 0
    · simp only [hx, zero_mul]
    · have hxS : x ∈ S := Or.inr (Set.mem_iUnion.mpr
        ⟨i, subset_tsupport (J i) hx⟩)
      dsimp only [b]
      rw [hχ1 x hxS, hχd x hxS i]
      ring
  have hFeq (x : EuclideanSpace ℝ (Fin n)) :
      F x * (χ x * η x) = F x * η x := by
    by_cases hx : F x = 0
    · simp only [hx, zero_mul]
    · have hxS : x ∈ S := Or.inl (subset_tsupport F hx)
      rw [hχ1 x hxS, one_mul]
  refine ⟨fun i => (hprod i).congr (Filter.Eventually.of_forall (hJeq i)),
    hforce.congr (Filter.Eventually.of_forall hFeq), ?_⟩
  calc
    _ = ∫ x, ∑ i : Fin n, J i x * b i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        Finset.sum_congr rfl fun i _ => (hJeq i x).symm
    _ = -(∫ x, F x * (χ x * η x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hEq
    _ = _ := congrArg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall hFeq))
