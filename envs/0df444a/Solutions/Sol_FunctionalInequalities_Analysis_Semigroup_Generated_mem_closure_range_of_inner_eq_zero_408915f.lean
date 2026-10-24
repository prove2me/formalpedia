-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:57:56.734759+00:00
-- url     : https://prove2.me/submissions/86f69293-bfb2-40ec-ba14-cf7e000c76d3

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
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_exists_mem_adjointComp_domain_of_inner_eq_zero_408915f

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
      FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_adjointComp_domain_of_inner_eq_zero_408915f T hT hd q hq'

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
