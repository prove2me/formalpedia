-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:58:27.300906+00:00
-- url     : https://prove2.me/submissions/6622a109-7ed6-40fd-a36d-734f297a6d0c

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
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_hasDerivWithinAt_apply_Iic_408915f

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
/-- The right time derivative at `t ≥ 0` is `-A(P_t f)`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.right_derivative
    (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ‖h⁻¹ • (apply T hT hd (t + h) f - apply T hT hd t f) +
        adjointComp T ⟨apply T hT hd t f,
          preserves_domain T hT hd f ht⟩‖ < ε := by
  obtain ⟨δ, hδ, he⟩ := generator_limit_apply T hT hd f ht hε
  refine ⟨δ, hδ, fun h hh hhδ => ?_⟩
  rw [generator_comm T hT hd f ht, add_comm t h, add_time T hT hd hh.le ht]
  exact he h hh hhδ
end
end
end
end
end
end

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
/-- **Right derivative of the orbit**: for `f ∈ D(A)` and `t ≥ 0`,
`d/ds P_s f = -A (P_t f)` from the right at `s = t`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Ici (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => apply T hT hd s f)
      (-adjointComp T ⟨apply T hT hd t f, preserves_domain T hT hd f ht⟩) (Ici t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := right_derivative T hT hd f ht hε
  refine ⟨δ, hδ, fun s hs hsd => ?_⟩
  have hs' : 0 < s - t := sub_pos.mpr hs
  have hlt : s - t < δ := by
    rw [Real.dist_eq, abs_of_pos hs'] at hsd; exact hsd
  rw [dist_eq_norm, slope_def_module, sub_neg_eq_add]
  have := h (s - t) hs' hlt
  rwa [add_sub_cancel] at this
/-- **Two-sided derivative of the orbit** at positive times. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply (f : (adjointComp T).domain) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => apply T hT hd s f)
      (-adjointComp T ⟨apply T hT hd t f, preserves_domain T hT hd f ht.le⟩) t := by
  have h := (hasDerivWithinAt_apply_Iic_408915f T hT hd f ht).union
    (hasDerivWithinAt_apply_Ici T hT hd f ht.le)
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.Semigroup.Generated in
/-- **Derivative of the orbit of arbitrary data** at positive times: for every `g` and `t > 0`,
`d/ds P_s g = -A (P_t g)` at `s = t`. Near `t` the orbit agrees with `s ↦ P_{s - t/2} F` for
`F = P_{t/2} g ∈ D(A)`. -/
theorem solution (g : H₀) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s g)
      (-FunctionalInequalities.Analysis.Semigroup.adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t g, FunctionalInequalities.Analysis.Semigroup.Generated.mem_adjointComp_domain_apply_of_pos T hT hd g ht⟩) t := by
  have hhalf : 0 < t / 2 := half_pos ht
  set F : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
    ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (t / 2) g, FunctionalInequalities.Analysis.Semigroup.Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hhalf⟩ with hFdef
  have h1 := FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply T hT hd F (show 0 < t - t / 2 by linarith)
  have h2 : HasDerivAt (fun s => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (s - t / 2) (F : H₀))
      (-FunctionalInequalities.Analysis.Semigroup.adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (t - t / 2) F,
        FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd F (by linarith)⟩) t := by
    have := HasDerivAt.scomp t h1 ((hasDerivAt_id' t).sub_const (t / 2))
    simpa [Function.comp_def] using this
  have heq : (⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (t - t / 2) F, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd F (by linarith)⟩ :
      (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) =
      ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t g, FunctionalInequalities.Analysis.Semigroup.Generated.mem_adjointComp_domain_apply_of_pos T hT hd g ht⟩ := by
    apply Subtype.ext
    simp only [hFdef]
    rw [← FunctionalInequalities.Analysis.Semigroup.Generated.add_time T hT hd (by linarith) hhalf.le]
    congr 1; ring
  rw [heq] at h2
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds (half_lt_self ht)] with s hs
  simp only [hFdef]
  rw [← FunctionalInequalities.Analysis.Semigroup.Generated.add_time T hT hd (by linarith) hhalf.le]
  congr 1; ring
