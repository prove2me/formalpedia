-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_of_mem_closure_range_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:29.765994+00:00
-- url     : https://prove2.me/submissions/1690e253-6453-49a8-854a-079533c90e9c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_tendsto_apply_adjointComp_readable

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- On the closure of the range of `A`, the semigroup converges strongly to `0`. -/
theorem solution {g : H₀}
    (hg : g ∈ closure (Set.range fun y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain => FunctionalInequalities.Analysis.Semigroup.adjointComp T y)) :
    Tendsto (fun t : ℝ => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t g) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨z, hz, hdist⟩ :=
    (Metric.mem_closure_iff.1 hg) (ε / 2) (by linarith)
  obtain ⟨y, rfl⟩ := hz
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 (FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_adjointComp_readable T hT hd y))
      (ε / 2) (by linarith)
  refine ⟨max N 0, ?_⟩
  intro t ht
  have htN : N ≤ t := le_trans (le_max_left N 0) ht
  have ht0 : 0 ≤ t := le_trans (le_max_right N 0) ht
  have hdist' : ‖g - FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ < ε / 2 := by
    simpa [dist_eq_norm] using hdist
  have hnorm' :
      ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T y)‖ < ε / 2 := by
    simpa [dist_eq_norm] using hN t htN
  have hmap :
      FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t g =
        FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (g - FunctionalInequalities.Analysis.Semigroup.adjointComp T y) +
          FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T y) := by
    rw [FunctionalInequalities.Analysis.Semigroup.Generated.map_sub T hT hd ht0]
    abel
  have hnorm : ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t g‖ < ε := by
    calc
      ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t g‖ =
          ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (g - FunctionalInequalities.Analysis.Semigroup.adjointComp T y) +
            FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T y)‖ := by rw [hmap]
      _ ≤ ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (g - FunctionalInequalities.Analysis.Semigroup.adjointComp T y)‖ +
            ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T y)‖ := norm_add_le _ _
      _ ≤ ‖g - FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ +
            ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T y)‖ := by
        gcongr
        exact FunctionalInequalities.Analysis.Semigroup.Generated.norm_apply_le T hT hd ht0 (g - FunctionalInequalities.Analysis.Semigroup.adjointComp T y)
      _ < ε := by linarith
  simpa [dist_eq_norm] using hnorm
