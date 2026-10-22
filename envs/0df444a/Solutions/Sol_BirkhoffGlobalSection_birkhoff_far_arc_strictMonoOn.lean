-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_arc_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T21:37:37.359453+00:00
-- url     : https://prove2.me/submissions/b16f29b3-7798-479d-a49f-404685da6de2

import Definitions.Def_BirkhoffShootingArcs
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_leviCivita_explicit_derivatives
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open BirkhoffGlobalSection Set Filter Topology

private lemma flow_line_hasDerivAt' (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c)
        ((φ t x : LeftEnergyState μ c) : Phase)) t := by
  have h0 : HasDerivAt (fun u : ℝ => ((φ u (φ t x) : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c)
        ((φ t x : LeftEnergyState μ c) : Phase)) (t - t) := by
    rw [sub_self]; exact hφ (φ t x)
  have h := HasDerivAt.comp_sub_const t t h0
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← Flow.map_add, sub_add_cancel]

private lemma mem_locus' {μ c : ℝ} (x : LeftEnergyState μ c) : (x : Phase) ∈ regularEnergyLocus μ c :=
  connectedComponentIn_subset _ _ x.2

/-- Position components of the Hamiltonian derivative, obtained from the platform's
proved explicit-gradient theorem. -/
private lemma flow_position_coords (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    let s := ((φ t x : LeftEnergyState μ c) : Phase)
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 0)
        (s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1 - μ * s 1) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 1)
        (s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0 - μ * s 0) t := by
  intro s
  have hc := hasDerivAt_pi.1 (flow_line_hasDerivAt' μ c φ hφ x t)
  have hs : s ∈ TangentialHessian.U := (mem_locus' (φ t x)).2
  have hd := (TangentialHessian.leviCivita_explicit_derivatives μ c).1 s hs
  constructor
  · refine (hc 0).congr_deriv ?_
    change hamiltonianVectorField (leviCivitaHamiltonian μ c) s _ = _
    simp [hamiltonianVectorField, hd, TangentialHessian.kGrad,
      TangentialHessian.kGradR, TangentialHessian.dP, TangentialHessian.dZ,
      TangentialHessian.dD]
    ring
  · refine (hc 1).congr_deriv ?_
    change hamiltonianVectorField (leviCivitaHamiltonian μ c) s _ = _
    simp [hamiltonianVectorField, hd, TangentialHessian.kGrad,
      TangentialHessian.kGradR, TangentialHessian.dP, TangentialHessian.dZ,
      TangentialHessian.dD]
    ring

/-- the horizontal relative position moves with the Jacobi horizontal velocity -/
private lemma xrel_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    let s := ((φ t x : LeftEnergyState μ c) : Phase)
    HasDerivAt (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0)
      (4 * (s 0 * s 2 - s 1 * s 3) - 16 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * s 1) t := by
  intro s
  obtain ⟨h0, h1⟩ := flow_position_coords μ c φ hφ x t
  have e : (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0) =
      fun u => 2 * (((φ u x : LeftEnergyState μ c) : Phase) 0 ^ 2 -
        ((φ u x : LeftEnergyState μ c) : Phase) 1 ^ 2) := by
    funext u; simp [relativePosition, leviCivitaPosition]
  rw [e]
  have := ((h0.fun_pow 2).fun_sub (h1.fun_pow 2)).const_mul 2
  refine this.congr_deriv ?_
  simp only [s]; ring


/-- Along a far arc the horizontal relative position is strictly increasing. -/
theorem solution (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (τ : ℝ)
    (h : IsFarShootingArc φ x τ) :
    StrictMonoOn
      (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0) (Icc 0 τ) := by
  obtain ⟨hτ, hlow, -, -, hv⟩ := h
  have hxd : ∀ t, HasDerivAt (fun u => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0) _ t :=
    fun t => xrel_hasDerivAt μ c φ hφ x t
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun t _ => (hxd t).continuousAt.continuousWithinAt)
  intro t ht
  rw [interior_Icc] at ht
  rw [(hxd t).deriv]
  have hy := hlow t ht
  have hvt := hv t ⟨ht.1, ht.2.le⟩
  generalize ((φ t x : LeftEnergyState μ c) : Phase) = s at hy hvt ⊢
  simp only [relativePosition, leviCivitaPosition, Matrix.cons_val_one] at hy
  have h0 : s 0 ≠ 0 := by rintro h; rw [h] at hy; simp at hy
  have hP : 0 < s 0 ^ 2 + s 1 ^ 2 := by positivity
  simp only [jacobiVelocity, leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum, zNormSq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at hvt
  have e : 4 * (s 0 * s 2 - s 1 * s 3) - 16 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * s 1 =
      4 * (s 0 ^ 2 + s 1 ^ 2) *
        ((s 2 * s 0 - s 3 * s 1) / (s 0 ^ 2 + s 1 ^ 2) - 4 * s 0 * s 1) := by
    field_simp; ring
  rw [e]; positivity

