-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_adjointComp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:29.436986+00:00
-- url     : https://prove2.me/submissions/0fd304b4-0d88-4d72-b80c-6f59d51fcf77

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Smoothing
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence

section
noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace LinearPMap
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- The generator bound behind `mem_adjointComp_domain_apply_of_pos`:
`t ‖T†T (P_t g)‖ ≤ ‖g‖` for arbitrary `g : H₀` and `t > 0`.  The sharp constant `1/(e t)` is not
claimed. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.mul_norm_adjointComp_apply_le (g : H₀) {t : ℝ} (ht : 0 < t)
    (h : apply T hT hd t g ∈ (adjointComp T).domain) :
    t * ‖adjointComp T ⟨apply T hT hd t g, h⟩‖ ≤ ‖g‖ := by
  obtain ⟨_, hle⟩ := exists_mem_adjointComp_domain_apply_of_pos T hT hd g ht
  exact hle
end
end
end

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- On the range of `A`, the semigroup converges strongly to `0`: `P_t (A y) → 0`. -/
theorem solution (y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) :
    Tendsto (fun t : ℝ => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T y)) atTop (𝓝 0) := by
  refine
    squeeze_zero_norm'
      (f := fun t : ℝ => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T y))
      (a := fun t : ℝ => ‖(y : H₀)‖ / t) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hdom : FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (y : H₀) ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
      FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd y ht.le
    have hmul :
        t * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (y : H₀), hdom⟩‖ ≤ ‖(y : H₀)‖ :=
      FunctionalInequalities.Analysis.Semigroup.Generated.mul_norm_adjointComp_apply_le T hT hd (y : H₀) ht hdom
    calc
      ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T y)‖ =
          ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (y : H₀), hdom⟩‖ := by
            rw [FunctionalInequalities.Analysis.Semigroup.Generated.generator_comm T hT hd y ht.le]
      _ ≤ ‖(y : H₀)‖ / t := (le_div_iff₀ ht).2 (by
        simpa [mul_comm] using hmul)
  · simpa using
      (tendsto_const_nhds.div_atTop
        (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
