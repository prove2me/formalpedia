-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_adjointComp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:58:13.692995+00:00
-- url     : https://prove2.me/submissions/29538ae9-e028-4360-8820-33568a7f56bb

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

section
noncomputable section
open InnerProductSpace
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
end
end
end

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
