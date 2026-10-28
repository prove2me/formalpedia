-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:28.352298+00:00
-- url     : https://prove2.me/submissions/2af80079-0a86-4210-bfbd-f8a3f95fa1db

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_exists_mem_adjointComp_domain_of_inner_eq_zero_readable

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
include hT hd in
/-- A vector orthogonal to the kernel of `A` lies in the closure of the range of `A`. -/
theorem solution (g : H₀)
    (hg : ∀ k : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain, FunctionalInequalities.Analysis.Semigroup.adjointComp T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
    g ∈ closure (Set.range fun y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain => FunctionalInequalities.Analysis.Semigroup.adjointComp T y) := by
  let R : Submodule ℝ H₀ := LinearMap.range (FunctionalInequalities.Analysis.Semigroup.adjointComp T).toFun

  have hgorth : g ∈ Rᗮᗮ := by
    apply (Submodule.mem_orthogonal' (Rᗮ) g).2
    intro q hq
    have hq' : ∀ y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain, ⟪q, FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ = 0 := by
      intro y
      have hy : FunctionalInequalities.Analysis.Semigroup.adjointComp T y ∈ R := by
        exact ⟨y, rfl⟩
      have hyorth : ⟪q, FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ = 0 :=
        (Submodule.mem_orthogonal' R q).1 hq (FunctionalInequalities.Analysis.Semigroup.adjointComp T y) hy
      exact hyorth

    obtain ⟨hdom, hzero⟩ :=
      FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_adjointComp_domain_of_inner_eq_zero_readable T hT hd q hq'

    have hzero_inner : ⟪g, q⟫ = 0 :=
      hg ⟨q, hdom⟩ hzero
    simpa [real_inner_comm] using hzero_inner

  have htop : g ∈ (R.topologicalClosure : Set H₀) := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure R]
    exact hgorth

  rw [Submodule.topologicalClosure_coe] at htop

  have hR :
      (R : Set H₀) = Set.range (fun y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain => FunctionalInequalities.Analysis.Semigroup.adjointComp T y) := by
    ext x
    constructor
    · intro hx
      exact hx
    · intro hx
      exact hx

  rw [hR] at htop
  exact htop
