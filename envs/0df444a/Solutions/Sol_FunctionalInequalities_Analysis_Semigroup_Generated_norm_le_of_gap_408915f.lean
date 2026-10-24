-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:57:09.495396+00:00
-- url     : https://prove2.me/submissions/0d761954-05bb-4d99-8a30-43108a912258

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
omit [CompleteSpace H₁] in
include hd in
/-- On the operator domain, `A y = 0` exactly when `T y = 0`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_eq_zero_iff (y : (adjointComp T).domain) :
    adjointComp T y = 0 ↔ T ⟨y, y.2.2⟩ = 0 := by
  constructor
  · intro hA
    have hnorm2 : ‖T ⟨(y : H₀), y.2.2⟩‖ ^ 2 = 0 := by
      rw [← inner_adjointComp_self hd y, hA, inner_zero_left]
    have hnorm : ‖T ⟨(y : H₀), y.2.2⟩‖ = 0 := by
      nlinarith [hnorm2]
    exact norm_eq_zero.mp hnorm
  · intro h
    refine hd.eq_zero_of_inner_left ℝ (fun z hz => ?_)
    rw [inner_adjointComp hd y hz, h, inner_zero_left]
end
end
end
end
end
end

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
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
omit [CompleteSpace H₁] in
include hd in
/-- On the operator domain, a gap inequality on `(ker T)ᗮ` gives the norm and energy bounds:
`‖u‖ ≤ C ‖A u‖`, `‖T u‖² = ⟪A u, u⟫` and `⟪A u, u⟫ ≤ C ‖A u‖²`. -/
theorem solution {C : ℝ}
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
    (u : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain)
    (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) :
    ‖(u : H₀)‖ ≤ C * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖ ∧
      ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 = ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T u, (u : H₀)⟫ ∧
      ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T u, (u : H₀)⟫ ≤ C * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖ ^ 2 := by
    have hgap' :
        ‖(u : H₀)‖ ^ 2 ≤ C * ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 :=
      hgap ⟨(u : H₀), u.2.2⟩ hu
    have henergy :
        ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 =
          ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T u, (u : H₀)⟫ :=
      (FunctionalInequalities.Analysis.Semigroup.inner_adjointComp_self (T := T) hd u).symm
    have hcs :
        ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T u, (u : H₀)⟫ ≤
          ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖ * ‖(u : H₀)‖ :=
      real_inner_le_norm _ _
    rcases le_total 0 C with hC | hC
    · by_cases hu0 : (u : H₀) = 0
      · have hz : (⟨(u : H₀), u.2.2⟩ : T.domain) = 0 := by
          apply Subtype.ext
          exact hu0
        have hTzero : T ⟨(u : H₀), u.2.2⟩ = 0 := by
          rw [hz]
          simp
        have hAu : FunctionalInequalities.Analysis.Semigroup.adjointComp T u = 0 :=
          (FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_eq_zero_iff T hd u).2 hTzero
        refine ⟨?_, henergy, ?_⟩
        · rw [hu0, hAu]
          simp
        · rw [hAu, hu0]
          simp
      · have hupos : 0 < ‖(u : H₀)‖ := norm_pos_iff.mpr hu0
        have hcsC :
            C * ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T u, (u : H₀)⟫ ≤
              C * (‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖ * ‖(u : H₀)‖) :=
          mul_le_mul_of_nonneg_left hcs hC
        have hnorm : ‖(u : H₀)‖ ≤ C * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖ := by
          by_contra hn
          have hlt : C * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖ < ‖(u : H₀)‖ :=
            lt_of_not_ge hn
          have hmul :
              C * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖ * ‖(u : H₀)‖ <
                ‖(u : H₀)‖ * ‖(u : H₀)‖ :=
            mul_lt_mul_of_pos_right hlt hupos
          nlinarith [hgap', henergy, hcsC, hmul]
        have hmul :
            ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖ * ‖(u : H₀)‖ ≤
              ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖ * (C * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T u‖) :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
        refine ⟨hnorm, henergy, ?_⟩
        nlinarith [hcs, hmul]
    · have hTnonneg :
          0 ≤ ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 :=
        sq_nonneg _
      have hCnonpos :
          C * ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC hTnonneg
      have hu_norm : ‖(u : H₀)‖ ^ 2 = 0 := by
        nlinarith [hgap', hCnonpos]
      have hu0 : (u : H₀) = 0 := by
        apply norm_eq_zero.mp
        nlinarith [hu_norm]
      have hz : (⟨(u : H₀), u.2.2⟩ : T.domain) = 0 := by
        apply Subtype.ext
        exact hu0
      have hTzero : T ⟨(u : H₀), u.2.2⟩ = 0 := by
        rw [hz]
        simp
      have hAu : FunctionalInequalities.Analysis.Semigroup.adjointComp T u = 0 :=
        (FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_eq_zero_iff T hd u).2 hTzero
      refine ⟨?_, henergy, ?_⟩
      · rw [hu0, hAu]
        simp
      · rw [hAu, hu0]
        simp
