-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:14.565234+00:00
-- url     : https://prove2.me/submissions/499b3b25-9ff2-4d95-9ce1-8a71c54fb4f8

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetProd_of_locally_memLp_two_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetSum_mul_readable

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
/-- The determinant of a bounded weak matrix field has its exact signed
permutation-polynomial directional derivative, locally in L2. -/
theorem solution {d : ℕ} {ι : Type*}
    [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (A x).det)
      (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  classical
  have hp (σ : Equiv.Perm ι) :=
    FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetProd_of_locally_memLp_two_readable
      (Finset.univ : Finset ι)
      (f := fun i x => A x (σ i) i)
      (df := fun i x => DA x (σ i) i)
      (v := v)
      (fun i _ => hA (σ i) i)
      (fun i _ => hbound (σ i) i)
      (fun i _ => hDA2 (σ i) i)
  have hs :=
    FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_readable
      (Finset.univ : Finset (Equiv.Perm ι))
      (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ))
      (f := fun σ x => ∏ i : ι, A x (σ i) i)
      (df := fun σ x => ∑ i : ι, DA x (σ i) i *
        ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j)
      (v := v)
      (fun σ _ => (hp σ).1)
      (fun σ _ => (hp σ).2)
  simpa only [Matrix.det_apply'] using hs
