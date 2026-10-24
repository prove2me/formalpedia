-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_eq_inner_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:57:57.838261+00:00
-- url     : https://prove2.me/submissions/f71963bd-c4d1-4253-af06-8273a5b3a0f7

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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.LinearPMap

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace
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
/-- The energy along the flow from `f ∈ D(A)` is `‖T (P_r f)‖² = ⟪P_r (A f), P_r f⟫`. -/
theorem solution (f : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) {r : ℝ} (hr : 0 ≤ r) :
    ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f, (FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hr).2⟩‖ ^ 2 =
      ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f⟫ := by
  let x : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
    ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hr⟩

  have hinner :
      ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T x, (x : H₀)⟫ =
        ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using
      (FunctionalInequalities.Analysis.Semigroup.inner_adjointComp (T := T) hd x x.2.2)

  have hgen :
      FunctionalInequalities.Analysis.Semigroup.adjointComp T x = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) := by
    dsimp [x]
    exact FunctionalInequalities.Analysis.Semigroup.Generated.generator_comm T hT hd f hr

  have hsub :
      (⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f, (FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hr).2⟩ : T.domain) =
        ⟨(x : H₀), x.2.2⟩ := by
    apply Subtype.ext
    rfl

  calc
    ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f, (FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hr).2⟩‖ ^ 2 =
        ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 := by rw [hsub]
    _ = ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T x, (x : H₀)⟫ := hinner.symm
    _ = ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f⟫ := by
      rw [hgen]
