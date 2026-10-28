-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_adjointComp_domain_of_inner_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:23.983981+00:00
-- url     : https://prove2.me/submissions/9c73c4ce-6011-4011-8023-ff994f3a2dfb

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
include hT hd in
/-- A vector orthogonal to the range of `A` lies in the kernel of `A` (self-adjointness). -/
theorem solution (q : H₀)
    (hq : ∀ y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain, ⟪q, FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ = 0) :
    ∃ h : q ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain, FunctionalInequalities.Analysis.Semigroup.adjointComp T ⟨q, h⟩ = 0 := by
  have hqdom : q ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T)†.domain := by
    rw [LinearPMap.mem_adjoint_domain_iff]
    have heq :
        (innerₛₗ ℝ q).comp (FunctionalInequalities.Analysis.Semigroup.adjointComp T).toFun = 0 := by
      ext y
      simpa using hq y
    rw [heq]
    exact continuous_zero

  have hzero : (FunctionalInequalities.Analysis.Semigroup.adjointComp T)† ⟨q, hqdom⟩ = 0 := by
    have h :=
      LinearPMap.adjoint_apply_eq
        (FunctionalInequalities.Analysis.Semigroup.dense_adjointComp_domain T hT hd) (⟨q, hqdom⟩ : (FunctionalInequalities.Analysis.Semigroup.adjointComp T)†.domain)
        (x₀ := (0 : H₀)) (by
          intro y
          simpa using (hq y).symm)
    exact h

  have hsa : (FunctionalInequalities.Analysis.Semigroup.adjointComp T)† = FunctionalInequalities.Analysis.Semigroup.adjointComp T :=
    (LinearPMap.isSelfAdjoint_def).1
      (FunctionalInequalities.Analysis.Semigroup.isSelfAdjoint_adjointComp T hT hd)
  obtain ⟨hdom, hval⟩ := LinearPMap.ext_iff.1 hsa
  have hqdom' : q ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain := by
    rw [← hdom]
    exact hqdom
  refine ⟨hqdom', ?_⟩
  have hv :
      (FunctionalInequalities.Analysis.Semigroup.adjointComp T)† ⟨q, hqdom⟩ =
        FunctionalInequalities.Analysis.Semigroup.adjointComp T ⟨q, hqdom'⟩ :=
    hval (x := q) (hf := hqdom) (hg := hqdom')
  rw [← hv]
  exact hzero
