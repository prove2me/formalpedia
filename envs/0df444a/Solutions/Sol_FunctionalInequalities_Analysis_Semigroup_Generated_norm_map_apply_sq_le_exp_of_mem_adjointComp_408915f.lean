-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_of_mem_adjointComp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:00:43.705399+00:00
-- url     : https://prove2.me/submissions/c4987a6c-702b-4510-9f8d-89a0af9e9bb0

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
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_continuousOn_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_hasDerivAt_inner_apply_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_le_exp_mul_of_hasDerivAt_le_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_map_apply_sq_eq_inner_408915f

section
noncomputable section
open InnerProductSpace
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
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
section
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
/-- **`P5`**: `P_0 = 1`.  `exp (-0 • L_s) = 1`, so the constant family `f` converges to `f`; `P1`
identifies the limit.  The route's `0 ≤ t` does not occur here. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.zero_time (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) : Generated.apply T hT hd 0 f = f := by
  refine (Generated.eq_apply_of_tendsto T hT hd le_rfl f f ?_).symm
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro s hs _
  have hid : NormedSpace.exp (-(0 : ℝ) • yosida T hT hs) f = f := by
    rw [neg_zero, zero_smul, NormedSpace.exp_zero]
    rfl
  rw [hid, sub_self, norm_zero]
  exact hε
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
/-- The energy `r ↦ ⟪P_r (A f), P_r f⟫` is continuous on `[0, ∞)`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn_inner_apply (f : (adjointComp T).domain) :
    ContinuousOn (fun r => ⟪apply T hT hd r (adjointComp T f), apply T hT hd r f⟫) (Ici 0) := by
  have h₁ :
      ContinuousOn (fun r => apply T hT hd r (adjointComp T f)) (Ici 0) :=
    Generated.continuousOn_408915f T hT hd (adjointComp T f)
  have h₂ :
      ContinuousOn (fun r => apply T hT hd r (f : H₀)) (Ici 0) :=
    Generated.continuousOn_408915f T hT hd (f : H₀)
  exact h₁.inner h₂
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.Semigroup.Generated in
/-- Exponential energy decay on `D(A)` under the curvature bound `ρ ‖T y‖² ≤ ‖A y‖²`. -/
theorem solution {ρ : ℝ}
    (hcurv : ∀ y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2)
    (f : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f, (FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f ht).2⟩‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ‖T ⟨f, f.2.2⟩‖ ^ 2 := by
  let E : ℝ → ℝ :=
    fun r => ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f⟫

  let E' : ℝ → ℝ := fun s =>
    if hs : 0 < s then
      -2 *
        ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T
          ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hs.le⟩‖ ^ 2
    else 0

  have hderiv : ∀ s, 0 < s → HasDerivAt E (E' s) s := by
    intro s hs
    have h := FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_inner_apply_408915f T hT hd f hs
    simpa [E, E', hs] using h

  have hle : ∀ s, 0 < s → E' s ≤ (-2 * ρ) * E s := by
    intro s hs
    rw [show E' s =
        -2 *
          ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T
            ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hs.le⟩‖ ^ 2 by
      simp [E', hs]]

    let y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
      ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hs.le⟩

    have hnorm : ‖T ⟨y, y.2.2⟩‖ ^ 2 = E s := by
      simpa [E, y] using
        (FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_eq_inner_408915f T hT hd f hs.le)

    have hcurv' :
        ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 :=
      hcurv y

    have hmain :
        -2 * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 ≤
          (-2 * ρ) * ‖T ⟨y, y.2.2⟩‖ ^ 2 := by
      linarith

    calc
      -2 *
          ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T
            ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hs.le⟩‖ ^ 2
          ≤ -2 * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
            rfl
      _ ≤ (-2 * ρ) * ‖T ⟨y, y.2.2⟩‖ ^ 2 := hmain
      _ = (-2 * ρ) * E s := by
        rw [hnorm]

  have hgronwall :
      E t ≤ Real.exp ((-2 * ρ) * t) * E 0 :=
    FunctionalInequalities.Analysis.Semigroup.Generated.le_exp_mul_of_hasDerivAt_le_408915f
      (E := E) (E' := E') (c := -2 * ρ)
      (FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn_inner_apply T hT hd f)
      hderiv hle ht

  have hzero : E 0 = ‖T ⟨f, f.2.2⟩‖ ^ 2 := by
    calc
      E 0 = ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T f, (f : H₀)⟫ := by
        dsimp [E]
        rw [FunctionalInequalities.Analysis.Semigroup.Generated.zero_time T hT hd (FunctionalInequalities.Analysis.Semigroup.adjointComp T f)]
        rw [FunctionalInequalities.Analysis.Semigroup.Generated.zero_time T hT hd (f : H₀)]
      _ = ‖T ⟨f, f.2.2⟩‖ ^ 2 := by
        rw [FunctionalInequalities.Analysis.Semigroup.inner_adjointComp (T := T) hd f f.2.2]
        rw [real_inner_self_eq_norm_sq]

  calc
    ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f, (FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f ht).2⟩‖ ^ 2 =
        E t := by
          simpa [E] using
            (FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_eq_inner_408915f T hT hd f ht)
    _ ≤ Real.exp ((-2 * ρ) * t) * E 0 := hgronwall
    _ = Real.exp (-2 * ρ * t) * ‖T ⟨f, f.2.2⟩‖ ^ 2 := by
      rw [hzero]
