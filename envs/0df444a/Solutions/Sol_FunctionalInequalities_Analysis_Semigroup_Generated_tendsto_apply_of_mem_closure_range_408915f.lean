-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_of_mem_closure_range_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:59:09.36661+00:00
-- url     : https://prove2.me/submissions/c45244b3-d70d-4b61-b675-6db0a1e3b606

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Dissipation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Smoothing
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.LinearPMap
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_tendsto_apply_adjointComp_408915f

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup
section
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.Semigroup.Generated in
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
    (Metric.tendsto_atTop.1 (FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_adjointComp_408915f T hT hd y))
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
