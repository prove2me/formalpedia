-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.euclideanMomentsFromCoordinates_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:55.806274+00:00
-- url     : https://prove2.me/submissions/7fc456da-650c-4749-9118-0392b8be4ab4

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.innerCoordinates {I : Type*} [Fintype I]
    (u p : EuclideanSpace ℝ I) : ⟪u, p⟫ = ∑ i, u i * p i := by
  simpa using ((EuclideanSpace.basisFun I ℝ).sum_inner_mul_inner u p).symm
 theorem solution {A I : Type*} [MeasurableSpace A]
    [Fintype I] [DecidableEq I] (ν : Measure A) [IsProbabilityMeasure ν] (Y : A → EuclideanSpace ℝ I)
    (hY : Measurable Y) (h2 : ∀ i, MemLp (fun x => Y x i) 2 ν)
    (h0 : ∀ i, (∫ x, Y x i ∂ν) = 0)
    (hcov : ∀ i j, (∫ x, Y x i * Y x j ∂ν) = if i = j then 1 else 0) :
    MemLp Y 2 ν ∧ (∫ x, Y x ∂ν) = 0 ∧
      ∀ u v : EuclideanSpace ℝ I, (∫ x, ⟪u, Y x⟫ * ⟪v, Y x⟫ ∂ν) = ⟪u, v⟫ := by
  classical
  have hsq (i : I) : Integrable (fun x => (Y x i) ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (h2 i).aestronglyMeasurable).mp (h2 i)
  have hY2 : MemLp Y 2 ν := by
    apply (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr
    simpa only [EuclideanSpace.real_norm_sq_eq] using
      integrable_finsetSum Finset.univ (fun i _ => hsq i)
  have hY0 : (∫ x, Y x ∂ν) = 0 := by
    ext i
    have hi := (EuclideanSpace.proj i : EuclideanSpace ℝ I →L[ℝ] ℝ).integral_comp_comm
      (hY2.integrable one_le_two)
    change (∫ x, Y x i ∂ν) = (∫ x, Y x ∂ν) i at hi
    rw [← hi, h0 i]
    rfl
  refine ⟨hY2, hY0, ?_⟩
  intro u v
  have hprod (i j : I) : Integrable (fun x => Y x i * Y x j) ν := by
    have h : MemLp (fun x => Y x i * Y x j) 1 ν := (h2 j).mul' (h2 i)
    exact h.integrable le_rfl
  have hterm (i j : I) : Integrable (fun x => (u i * v j) * (Y x i * Y x j)) ν :=
    (hprod i j).const_mul _
  have hexpand (x : A) : ⟪u, Y x⟫ * ⟪v, Y x⟫ =
      ∑ i : I, ∑ j : I, (u i * v j) * (Y x i * Y x j) := by
    rw [FunctionalInequalities.KLS.LogConcave.Suspension.innerCoordinates, FunctionalInequalities.KLS.LogConcave.Suspension.innerCoordinates, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    (∫ x, ⟪u, Y x⟫ * ⟪v, Y x⟫ ∂ν) =
        ∫ x, ∑ i : I, ∑ j : I, (u i * v j) * (Y x i * Y x j) ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i : I, ∑ j : I, ∫ x, (u i * v j) * (Y x i * Y x j) ∂ν := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum _ (fun j _ => hterm i j)
    _ = ∑ i : I, ∑ j : I, (u i * v j) * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul, hcov i j]
    _ = ∑ i : I, u i * v i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
    _ = ⟪u, v⟫ := (FunctionalInequalities.KLS.LogConcave.Suspension.innerCoordinates u v).symm
