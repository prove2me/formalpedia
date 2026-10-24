-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_inner_apply_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:59:37.726044+00:00
-- url     : https://prove2.me/submissions/09e9bc5b-ec6c-4de5-a78f-e91406dcebba

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
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_hasDerivAt_apply_of_pos_408915f

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
/-- The energy derivative: for `f ∈ D(A)` and `s > 0`,
`d/ds ⟪P_s (A f), P_s f⟫ = -2 ‖A (P_s f)‖²`. -/
theorem solution (f : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r => ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f⟫)
      (-2 * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hs.le⟩‖ ^ 2) s := by
  let y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
    ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hs.le⟩

  let z : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
    ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f),
      FunctionalInequalities.Analysis.Semigroup.Generated.mem_adjointComp_domain_apply_of_pos T hT hd (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) hs⟩

  have hgen : FunctionalInequalities.Analysis.Semigroup.adjointComp T y = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) := by
    dsimp [y]
    exact FunctionalInequalities.Analysis.Semigroup.Generated.generator_comm T hT hd f hs.le

  have hz : (z : H₀) = FunctionalInequalities.Analysis.Semigroup.adjointComp T y := by
    dsimp [z]
    exact hgen.symm

  have h1 :
      HasDerivAt (fun r => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f))
        (-FunctionalInequalities.Analysis.Semigroup.adjointComp T z) s := by
    dsimp [z]
    exact FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos_408915f T hT hd (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) hs

  have h2 :
      HasDerivAt (fun r => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (f : H₀))
        (-FunctionalInequalities.Analysis.Semigroup.adjointComp T y) s := by
    dsimp [y]
    exact FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos_408915f T hT hd (f : H₀) hs

  have hsymm :
      ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z, (y : H₀)⟫ =
        ⟪(z : H₀), FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
    calc
      ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z, (y : H₀)⟫ =
          ⟪T ⟨(z : H₀), z.2.2⟩, T ⟨(y : H₀), y.2.2⟩⟫ :=
        FunctionalInequalities.Analysis.Semigroup.inner_adjointComp (T := T) hd z y.2.2
      _ = ⟪T ⟨(y : H₀), y.2.2⟩, T ⟨(z : H₀), z.2.2⟩⟫ := by
        rw [real_inner_comm]
      _ = ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T y, (z : H₀)⟫ :=
        (FunctionalInequalities.Analysis.Semigroup.inner_adjointComp (T := T) hd y z.2.2).symm
      _ = ⟪(z : H₀), FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [real_inner_comm]

  have hfirst :
      ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), -FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ =
        -‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
    calc
      ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), -FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ =
          ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T y, -FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [hgen]
      _ = -⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T y, FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [inner_neg_right]
      _ = -‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]

  have hsecond :
      ⟪-FunctionalInequalities.Analysis.Semigroup.adjointComp T z, FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f⟫ =
        -‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
    calc
      ⟪-FunctionalInequalities.Analysis.Semigroup.adjointComp T z, FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f⟫ =
          -⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z, (y : H₀)⟫ := by
        dsimp [y]
        rw [inner_neg_left]
      _ = -⟪(z : H₀), FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [hsymm]
      _ = -⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T y, FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [hz]
      _ = -‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]

  have hder :=
    h1.inner ℝ h2

  have heq :
      ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), -FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ +
          ⟪-FunctionalInequalities.Analysis.Semigroup.adjointComp T z, FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f⟫ =
        -2 * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
    rw [hfirst, hsecond]
    ring

  have hresult :
      HasDerivAt
        (fun r => ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f⟫)
        (-2 * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2) s :=
    hder.congr_deriv heq

  simpa [y] using hresult
