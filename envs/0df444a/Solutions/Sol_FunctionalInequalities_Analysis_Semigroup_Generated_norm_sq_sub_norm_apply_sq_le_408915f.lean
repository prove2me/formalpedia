-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.norm_sq_sub_norm_apply_sq_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:02:59.669831+00:00
-- url     : https://prove2.me/submissions/a852dd8c-e60f-422d-94a3-ffb47174907d

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
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_hasDerivAt_apply_of_pos_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_map_apply_sq_le_exp_408915f

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
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.Semigroup.Generated in
/-- The finite-time Poincaré bound under the curvature bound with `ρ > 0`: for `f ∈ D(T)` and
`t ≥ 0`, `‖f‖² - ‖P_t f‖² ≤ (1 - e^{-2ρt}) / ρ · ‖T f‖²`. -/
theorem solution {ρ : ℝ} (hρ : 0 < ρ)
    (hcurv : ∀ y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2)
    (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖(f : H₀)‖ ^ 2 - ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ * ‖T f‖ ^ 2 := by
  let E0 : ℝ := ‖T f‖ ^ 2
  let φ : ℝ → ℝ := fun s =>
    ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀)‖ ^ 2 -
      Real.exp (-2 * ρ * s) * (E0 / ρ)

  have hcont_exp :
      ContinuousOn (fun s : ℝ => Real.exp (-2 * ρ * s)) (Ici 0) := by
    have harg : Continuous (fun s : ℝ => -2 * ρ * s) := by
      have hmul :
          Continuous (fun s : ℝ => (-2 * ρ) * s) :=
        (continuous_const.mul continuous_id :
          Continuous (fun s : ℝ => (-2 * ρ) * s))
      simpa [mul_assoc] using hmul
    have hcomp :
        Continuous (fun s : ℝ => Real.exp ((fun x : ℝ => -2 * ρ * x) s)) :=
      Real.continuous_exp.comp harg
    simpa only [Function.comp_apply] using hcomp.continuousOn

  have hcont : ContinuousOn φ (Ici 0) := by
    have hnorm :
        ContinuousOn
          (fun s : ℝ => ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀)‖ ^ 2) (Ici 0) :=
      (FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn_408915f T hT hd (f : H₀)).norm.pow 2
    have hterm :
        ContinuousOn
          (fun s : ℝ => Real.exp (-2 * ρ * s) * (E0 / ρ)) (Ici 0) :=
      hcont_exp.mul continuousOn_const
    exact hnorm.sub hterm

  let D : ℝ → ℝ := fun s =>
    if hs : 0 < s then
      -2 *
          ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀),
            FunctionalInequalities.Analysis.Semigroup.Generated.preserves_form_domain T hT hd f hs.le⟩‖ ^ 2 +
        2 * Real.exp (-2 * ρ * s) * E0
    else 0

  have hderiv : ∀ s, 0 < s → HasDerivAt φ (D s) s := by
    intro s hs
    let z : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
      ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀),
        FunctionalInequalities.Analysis.Semigroup.Generated.mem_adjointComp_domain_apply_of_pos T hT hd (f : H₀) hs⟩

    have hinner :
        ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀), -FunctionalInequalities.Analysis.Semigroup.adjointComp T z⟫ =
          -‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀), z.2.2⟩‖ ^ 2 := by
      calc
        ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀), -FunctionalInequalities.Analysis.Semigroup.adjointComp T z⟫ =
            -⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀), FunctionalInequalities.Analysis.Semigroup.adjointComp T z⟫ := by
              rw [inner_neg_right]
        _ = -⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z, FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀)⟫ := by
              rw [real_inner_comm]
        _ = -⟪T ⟨(z : H₀), z.2.2⟩, T ⟨(z : H₀), z.2.2⟩⟫ := by
              rw [FunctionalInequalities.Analysis.Semigroup.inner_adjointComp (T := T) hd z z.2.2]
        _ = -‖T ⟨(z : H₀), z.2.2⟩‖ ^ 2 := by
              rw [real_inner_self_eq_norm_sq]
        _ = -‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀), z.2.2⟩‖ ^ 2 := by
              rfl

    have hnorm :
        HasDerivAt
          (fun r : ℝ => ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (f : H₀)‖ ^ 2)
          (-2 * ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀), z.2.2⟩‖ ^ 2) s := by
      have h :=
        (FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos_408915f T hT hd (f : H₀) hs).norm_sq
      exact h.congr_deriv (by
        rw [hinner]
        ring)

    have harg :
        HasDerivAt (fun r : ℝ => -(2 * ρ * r)) (-(2 * ρ)) s := by
      simpa only [mul_one] using
        ((hasDerivAt_id' s).const_mul (2 * ρ)).fun_neg

    have hexp :
        HasDerivAt (fun r : ℝ => Real.exp (-(2 * ρ * r)))
          (Real.exp (-(2 * ρ * s)) * (-(2 * ρ))) s :=
      harg.exp

    have hconst :
        HasDerivAt (fun _ : ℝ => E0 / ρ) 0 s :=
      hasDerivAt_const (x := s) (c := E0 / ρ)

    have hterm :
        HasDerivAt
          (fun r : ℝ => Real.exp (-(2 * ρ * r)) * (E0 / ρ))
          (-2 * Real.exp (-(2 * ρ * s)) * E0) s := by
      have h := hexp.fun_mul hconst
      exact h.congr_deriv (by
        field_simp [hρ.ne']
        ring)

    have hsub := hnorm.sub hterm
    have hsub' :
        HasDerivAt
          (fun r : ℝ =>
            ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (f : H₀)‖ ^ 2 -
              Real.exp (-(2 * ρ * r)) * (E0 / ρ))
          (-2 * ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀), z.2.2⟩‖ ^ 2 +
            2 * Real.exp (-(2 * ρ * s)) * E0) s :=
      hsub.congr_deriv (by ring)
    simpa [φ, D, hs, z] using hsub'

  have hnonneg : ∀ s ∈ interior (Ici (0 : ℝ)), 0 ≤ D s := by
    intro s hs
    have hs' : 0 < s := by
      simpa [interior_Ici] using hs
    dsimp [D]
    rw [dif_pos hs']
    have hdec :=
      FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_408915f T hT hd hcurv f hs'.le
    have hdec' :
        ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (f : H₀),
            FunctionalInequalities.Analysis.Semigroup.Generated.preserves_form_domain T hT hd f hs'.le⟩‖ ^ 2 ≤
          Real.exp (-2 * ρ * s) * E0 := by
      simpa [E0] using hdec
    linarith

  have hmono : MonotoneOn φ (Ici (0 : ℝ)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Ici (0 : ℝ)) (f := φ) (f' := D)
      (convex_Ici (0 : ℝ)) hcont ?_ hnonneg
    intro s hs
    have hs' : 0 < s := by
      simpa [interior_Ici] using hs
    exact (hderiv s hs').hasDerivWithinAt

  have hφ : φ 0 ≤ φ t := by
    exact hmono (by simp) ht ht

  have hφ' :
      ‖(f : H₀)‖ ^ 2 - E0 / ρ ≤
        ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (f : H₀)‖ ^ 2 -
          Real.exp (-2 * ρ * t) * (E0 / ρ) := by
    have hzero := FunctionalInequalities.Analysis.Semigroup.Generated.zero_time T hT hd (f : H₀)
    simpa [φ, hzero, Real.exp_zero] using hφ

  have hmain :
      ‖(f : H₀)‖ ^ 2 - ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (f : H₀)‖ ^ 2 ≤
        E0 / ρ - Real.exp (-2 * ρ * t) * (E0 / ρ) := by
    linarith

  calc
    ‖(f : H₀)‖ ^ 2 - ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f‖ ^ 2
        ≤ E0 / ρ - Real.exp (-2 * ρ * t) * (E0 / ρ) := by
          simpa using hmain
    _ = (1 - Real.exp (-2 * ρ * t)) / ρ * ‖T f‖ ^ 2 := by
      dsimp [E0]
      field_simp [hρ.ne']
