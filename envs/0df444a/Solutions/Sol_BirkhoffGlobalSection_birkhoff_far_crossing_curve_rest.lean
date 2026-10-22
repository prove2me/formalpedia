-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_crossing_curve_rest
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T19:03:47.708448+00:00
-- url     : https://prove2.me/submissions/f3ec64c4-4ae1-4dfe-898f-b300507f1f91

import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_end_rest
import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffShootingCoordinates
import Theorems.Thm_BirkhoffGlobalSection_partial_derivative_eq_update_deriv
import Theorems.Thm_BirkhoffGlobalSection_leftCollisionPoint_mem_leftEnergyComponent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
import Definitions.Def_BirkhoffShootingArcs
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_continuity
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_small

open BirkhoffGlobalSection Set Filter Topology Function

-- ===== Solutions.CM =====
/-- differentiability of the regularized Hamiltonian away from the second collision -/
lemma K_differentiableAt (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    DifferentiableAt ℝ (leviCivitaHamiltonian μ c) s := by
  have hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  unfold leviCivitaHamiltonian wNormSq zNormSq
  have hsq : DifferentiableAt ℝ (fun s : Phase => Real.sqrt (secondCollisionDistanceSq s)) s := by
    unfold secondCollisionDistanceSq at hD ⊢
    exact (by fun_prop : DifferentiableAt ℝ (fun s : Phase =>
      (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) s).sqrt hD.ne'
  fun_prop (disch := assumption)

lemma K_line0 (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    HasDerivAt (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 0 t))
      (2 * c * s 0 + 4 * s 0 * (s 0 * s 3 - s 1 * s 2) + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 3
        - μ * s 3 - μ * (2 * s 0 / Real.sqrt (secondCollisionDistanceSq s)
          - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1) /
            Real.sqrt (secondCollisionDistanceSq s) ^ 3)) (s 0) := by
  have e : (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 0 t)) =
      fun t => (s 2 ^ 2 + s 3 ^ 2) / 2 + c * (t ^ 2 + s 1 ^ 2) - (1 - μ) / 2
        + 2 * (t ^ 2 + s 1 ^ 2) * (t * s 3 - s 1 * s 2) - μ * (t * s 3 + s 1 * s 2)
        - μ * (t ^ 2 + s 1 ^ 2) / Real.sqrt ((2 * (t ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * t * s 1) ^ 2) := by
    funext t
    simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq, Function.update]
  rw [e]
  have hx := hasDerivAt_id' (s 0)
  have hin : HasDerivAt (fun t : ℝ => (2 * (t ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * t * s 1) ^ 2)
      (8 * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1)) (s 0) := by
    have := ((((hx.fun_pow 2).sub_const (s 1 ^ 2)).const_mul 2).sub_const 1).fun_pow 2
      |>.fun_add (((hx.const_mul 4).mul_const (s 1)).fun_pow 2)
    refine this.congr_deriv ?_
    simp; ring
  have hD' : (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2 ≠ 0 := hD.ne'
  have hS := hin.sqrt hD'
  have hNpos : 0 < Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) :=
    Real.sqrt_pos.2 hD
  have hsq := Real.sq_sqrt hD.le
  have hP := (hx.fun_pow 2).add_const (s 1 ^ 2)
  have htot := (((((hP.const_mul c).const_add ((s 2 ^ 2 + s 3 ^ 2) / 2)).sub_const ((1 - μ) / 2)).fun_add
    ((hP.const_mul 2).fun_mul ((hx.mul_const (s 3)).sub_const (s 1 * s 2)))).fun_sub
    ((hx.mul_const (s 3)).add_const (s 1 * s 2) |>.const_mul μ)).fun_sub
    ((hP.const_mul μ).fun_div hS hNpos.ne')
  refine htot.congr_deriv ?_
  unfold secondCollisionDistanceSq at hsq ⊢
  generalize Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) = N at *
  have hNne : N ≠ 0 := hNpos.ne'
  field_simp
  ring

lemma K_line1 (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    HasDerivAt (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 1 t))
      (2 * c * s 1 + 4 * s 1 * (s 0 * s 3 - s 1 * s 2) - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 2
        - μ * s 2 - μ * (2 * s 1 / Real.sqrt (secondCollisionDistanceSq s)
          - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1) /
            Real.sqrt (secondCollisionDistanceSq s) ^ 3)) (s 1) := by
  have e : (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 1 t)) =
      fun t => (s 2 ^ 2 + s 3 ^ 2) / 2 + c * (s 0 ^ 2 + t ^ 2) - (1 - μ) / 2
        + 2 * (s 0 ^ 2 + t ^ 2) * (s 0 * s 3 - t * s 2) - μ * (s 0 * s 3 + t * s 2)
        - μ * (s 0 ^ 2 + t ^ 2) / Real.sqrt ((2 * (s 0 ^ 2 - t ^ 2) - 1) ^ 2 + (4 * s 0 * t) ^ 2) := by
    funext t
    simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq, Function.update]
  rw [e]
  have hx := hasDerivAt_id' (s 1)
  have hin : HasDerivAt (fun t : ℝ => (2 * (s 0 ^ 2 - t ^ 2) - 1) ^ 2 + (4 * s 0 * t) ^ 2)
      (8 * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1)) (s 1) := by
    have := ((((hx.fun_pow 2).const_sub (s 0 ^ 2)).const_mul 2).sub_const 1).fun_pow 2
      |>.fun_add ((hx.const_mul (4 * s 0)).fun_pow 2)
    refine this.congr_deriv ?_
    simp; ring
  have hD' : (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2 ≠ 0 := hD.ne'
  have hS := hin.sqrt hD'
  have hNpos : 0 < Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) :=
    Real.sqrt_pos.2 hD
  have hsq := Real.sq_sqrt hD.le
  have hP := (hx.fun_pow 2).const_add (s 0 ^ 2)
  have htot := (((((hP.const_mul c).const_add ((s 2 ^ 2 + s 3 ^ 2) / 2)).sub_const ((1 - μ) / 2)).fun_add
    ((hP.const_mul 2).fun_mul ((hx.mul_const (s 2)).const_sub (s 0 * s 3)))).fun_sub
    ((hx.mul_const (s 2)).const_add (s 0 * s 3) |>.const_mul μ)).fun_sub
    ((hP.const_mul μ).fun_div hS hNpos.ne')
  refine htot.congr_deriv ?_
  unfold secondCollisionDistanceSq at hsq ⊢
  generalize Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) = N at *
  have hNne : N ≠ 0 := hNpos.ne'
  field_simp
  ring

lemma K_line2 (μ c : ℝ) (s : Phase) :
    HasDerivAt (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 2 t))
      (s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1 - μ * s 1) (s 2) := by
  have e : (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 2 t)) =
      fun t => (t ^ 2 + s 3 ^ 2) / 2 + c * (s 0 ^ 2 + s 1 ^ 2) - (1 - μ) / 2
        + 2 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * s 3 - s 1 * t) - μ * (s 0 * s 3 + s 1 * t)
        - μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s) := by
    funext t
    simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq, Function.update]
  rw [e]
  have hx := hasDerivAt_id' (s 2)
  have := ((((((hx.fun_pow 2).add_const (s 3 ^ 2)).div_const 2).add_const (c * (s 0 ^ 2 + s 1 ^ 2))).sub_const
    ((1 - μ) / 2)).fun_add (((hx.const_mul (s 1)).const_sub (s 0 * s 3)).const_mul
      (2 * (s 0 ^ 2 + s 1 ^ 2)))).fun_sub (((hx.const_mul (s 1)).const_add (s 0 * s 3)).const_mul μ)
    |>.sub_const (μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s))
  refine this.congr_deriv ?_
  simp; try ring

lemma K_line3 (μ c : ℝ) (s : Phase) :
    HasDerivAt (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 3 t))
      (s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0 - μ * s 0) (s 3) := by
  have e : (fun t : ℝ => leviCivitaHamiltonian μ c (Function.update s 3 t)) =
      fun t => (s 2 ^ 2 + t ^ 2) / 2 + c * (s 0 ^ 2 + s 1 ^ 2) - (1 - μ) / 2
        + 2 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * t - s 1 * s 2) - μ * (s 0 * t + s 1 * s 2)
        - μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s) := by
    funext t
    simp [leviCivitaHamiltonian, wNormSq, zNormSq, secondCollisionDistanceSq, Function.update]
  rw [e]
  have hx := hasDerivAt_id' (s 3)
  have := ((((((hx.fun_pow 2).const_add (s 2 ^ 2)).div_const 2).add_const (c * (s 0 ^ 2 + s 1 ^ 2))).sub_const
    ((1 - μ) / 2)).fun_add (((hx.const_mul (s 0)).sub_const (s 1 * s 2)).const_mul
      (2 * (s 0 ^ 2 + s 1 ^ 2)))).fun_sub (((hx.const_mul (s 0)).add_const (s 1 * s 2)).const_mul μ)
    |>.sub_const (μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s))
  refine this.congr_deriv ?_
  simp; try ring

/-- Explicit Hamiltonian vector field of the regularized Hamiltonian. -/
lemma K_hvf (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    hamiltonianVectorField (leviCivitaHamiltonian μ c) s =
      ![s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1 - μ * s 1,
        s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0 - μ * s 0,
        -(2 * c * s 0 + 4 * s 0 * (s 0 * s 3 - s 1 * s 2) + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 3
          - μ * s 3 - μ * (2 * s 0 / Real.sqrt (secondCollisionDistanceSq s)
            - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1) /
              Real.sqrt (secondCollisionDistanceSq s) ^ 3)),
        -(2 * c * s 1 + 4 * s 1 * (s 0 * s 3 - s 1 * s 2) - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 2
          - μ * s 2 - μ * (2 * s 1 / Real.sqrt (secondCollisionDistanceSq s)
            - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1) /
              Real.sqrt (secondCollisionDistanceSq s) ^ 3))] := by
  have hd := K_differentiableAt μ c s hD
  unfold hamiltonianVectorField
  rw [partial_derivative_eq_update_deriv _ _ _ hd, partial_derivative_eq_update_deriv _ _ _ hd,
    partial_derivative_eq_update_deriv _ _ _ hd, partial_derivative_eq_update_deriv _ _ _ hd,
    (K_line0 μ c s hD).deriv, (K_line1 μ c s hD).deriv, (K_line2 μ c s).deriv, (K_line3 μ c s).deriv]

lemma flow_line_hasDerivAt' (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
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
  rw [← Flow.map_add]; congr 1; ring

lemma mem_locus' {μ c : ℝ} (x : LeftEnergyState μ c) : (x : Phase) ∈ regularEnergyLocus μ c :=
  connectedComponentIn_subset _ _ x.2

/-- coordinate derivatives along a flow line -/
lemma flow_coords (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    let s := ((φ t x : LeftEnergyState μ c) : Phase)
    let N := Real.sqrt (secondCollisionDistanceSq s)
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 0)
        (s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1 - μ * s 1) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 1)
        (s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0 - μ * s 0) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 2)
        (-(2 * c * s 0 + 4 * s 0 * (s 0 * s 3 - s 1 * s 2) + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 3
          - μ * s 3 - μ * (2 * s 0 / N
            - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1) / N ^ 3))) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 3)
        (-(2 * c * s 1 + 4 * s 1 * (s 0 * s 3 - s 1 * s 2) - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 2
          - μ * s 2 - μ * (2 * s 1 / N
            - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1) / N ^ 3))) t := by
  intro s N
  have h := flow_line_hasDerivAt' μ c φ hφ x t
  rw [K_hvf μ c _ (mem_locus' (φ t x)).2] at h
  have hc := hasDerivAt_pi.1 h
  exact ⟨by simpa using hc 0, by simpa using hc 1, by simpa using hc 2, by simpa using hc 3⟩

/-- the horizontal relative position moves with the Jacobi horizontal velocity -/
lemma xrel_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    let s := ((φ t x : LeftEnergyState μ c) : Phase)
    HasDerivAt (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0)
      (4 * (s 0 * s 2 - s 1 * s 3) - 16 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * s 1) t := by
  intro s
  obtain ⟨h0, h1, -, -⟩ := flow_coords μ c φ hφ x t
  have e : (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0) =
      fun u => 2 * (((φ u x : LeftEnergyState μ c) : Phase) 0 ^ 2 -
        ((φ u x : LeftEnergyState μ c) : Phase) 1 ^ 2) := by
    funext u; simp [relativePosition, leviCivitaPosition]
  rw [e]
  have := ((h0.fun_pow 2).fun_sub (h1.fun_pow 2)).const_mul 2
  refine this.congr_deriv ?_
  simp only [s]; ring

noncomputable def Vx (s : Phase) : ℝ := (s 2 * s 0 - s 3 * s 1) / (s 0 ^ 2 + s 1 ^ 2) - 4 * s 0 * s 1

noncomputable def Vy (μ : ℝ) (s : Phase) : ℝ :=
  (s 2 * s 1 + s 3 * s 0) / (s 0 ^ 2 + s 1 ^ 2) + 2 * (s 0 ^ 2 - s 1 ^ 2) - μ

/-- the Jacobi potential force components at the physical position of a Levi-Civita state -/
noncomputable def Omx (μ : ℝ) (s : Phase) : ℝ :=
  (2 * (s 0 ^ 2 - s 1 ^ 2) - μ) -
    (1 - μ) * (2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) /
      Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3 -
    μ * (2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) /
      Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 3

-- ===== Solutions.Abstract =====
section Abstract

variable {X : Type*} [TopologicalSpace X]

-- ===== Solutions.CM7 =====
/-- Along a far arc the horizontal relative position is strictly increasing. -/
lemma far_arc_mono (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
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
  simp only [relativePosition, leviCivitaPosition, Matrix.cons_val_one, Matrix.head_cons] at hy
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


attribute [local irreducible] Omx Vy Vx zNormSq in
-- ===== Solutions.CM29 =====
/-! Birkhoff's identity (59): the angular momentum about the primary along far arcs. -/

-- ===== Solutions.CM36 =====
/-- The first bad parameter of an open-at-good-points family that is good near `0`. -/
lemma first_bad_parameter (G : ℝ → Prop)
    (hopen : ∀ r₀ > 0, G r₀ → ∃ δ > 0, ∀ r : ℝ, |r - r₀| < δ → G r)
    (hsmall : ∃ ε > 0, ∀ r ∈ Ioo 0 ε, G r) (R : ℝ) (hR : 0 < R) (hbadR : ¬ G R) :
    ∃ b > 0, (∀ r ∈ Ioo 0 b, G r) ∧ ¬ G b := by
  obtain ⟨ε, hε, hεG⟩ := hsmall
  set A : Set ℝ := {b' | 0 < b' ∧ ∀ r ∈ Ioo 0 b', G r} with hA
  have hεA : ε ∈ A := ⟨hε, hεG⟩
  have hbdd : BddAbove A := by
    refine ⟨R, fun b' hb' => ?_⟩
    by_contra h
    push Not at h
    exact hbadR (hb'.2 R ⟨hR, h⟩)
  set b := sSup A
  have hεb : ε ≤ b := le_csSup hbdd hεA
  have hgood : ∀ r ∈ Ioo 0 b, G r := by
    intro r hr
    obtain ⟨b', hb', hrb'⟩ := exists_lt_of_lt_csSup ⟨ε, hεA⟩ hr.2
    exact hb'.2 r ⟨hr.1, hrb'⟩
  refine ⟨b, lt_of_lt_of_le hε hεb, hgood, fun hGb => ?_⟩
  obtain ⟨δ, hδ, hδG⟩ := hopen b (lt_of_lt_of_le hε hεb) hGb
  have hmem : b + δ / 2 ∈ A := by
    refine ⟨by linarith, fun r hr => ?_⟩
    rcases lt_or_ge r b with h | h
    · exact hgood r ⟨hr.1, h⟩
    · exact hδG r (by rw [abs_lt]; constructor <;> linarith [hr.2])
  have := le_csSup hbdd hmem
  linarith

/-- differentiability of the regularized Hamiltonian away from the second collision -/

lemma farStart_coords (μ c r : ℝ) :
    farShootingStart μ c r 0 = 0 ∧ farShootingStart μ c r 1 = r ∧
      farShootingStart μ c r 3 = 0 := by
  simp [farShootingStart]


lemma far_arc_unique (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c)
    (τ₁ τ₂ : ℝ) (h₁ : IsFarShootingArc φ x τ₁) (h₂ : IsFarShootingArc φ x τ₂) : τ₁ = τ₂ := by
  rcases lt_trichotomy τ₁ τ₂ with h | h | h
  · have := far_arc_mono μ c φ hφ x τ₂ h₂ ⟨h₁.1.le, h.le⟩ ⟨h₂.1.le, le_refl _⟩ h
    simp only at this; rw [h₁.2.2.2.1, h₂.2.2.2.1] at this; exact absurd this (lt_irrefl 0)
  · exact h
  · have := far_arc_mono μ c φ hφ x τ₁ h₁ ⟨h₂.1.le, h.le⟩ ⟨h₁.1.le, le_refl _⟩ h
    simp only at this; rw [h₁.2.2.2.1, h₂.2.2.2.1] at this; exact absurd this (lt_irrefl 0)


theorem far_crossing_curve_rest (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ b : ℝ, 0 < b ∧ ∃ E : ℝ × ℝ, ∃ S : ℝ → LeftEnergyState μ c, ∃ T : ℝ → ℝ,
      ContinuousOn (fun r : ℝ =>
        shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) (Set.Ioo 0 b) ∧
      Filter.Tendsto (fun r : ℝ =>
        shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(Real.sqrt 2 / 2), 0)) ∧
      (((((E.1 = -1 ∨ E.1 = 1) ∧ 0 < E.2) ∨ (E.2 = 0 ∧ Real.sqrt 2 / 2 < E.1)) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin b (Set.Iio b)) (nhds E)) ∨
       (0 < E.2 ∧
        (∀ s : LeftEnergyState μ c, relativePosition μ (s : Phase) 0 = 0 →
          relativePosition μ (s : Phase) 1 < 0 →
          0 < jacobiVelocity (leviCivitaToJacobi μ (s : Phase)) 0 →
          -relativePosition μ (s : Phase) 1 < E.2) ∧
        Filter.Tendsto (fun r : ℝ =>
          (shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)).2)
          (nhdsWithin b (Set.Iio b)) (nhds E.2))) ∧
      ∀ r ∈ Set.Ioo 0 b,
        ((S r : LeftEnergyState μ c) : Phase) 0 = 0 ∧
        ((S r : LeftEnergyState μ c) : Phase) 3 = 0 ∧
        ((S r : LeftEnergyState μ c) : Phase) 1 ≠ 0 ∧
        0 < T r ∧
        (∀ u ∈ Set.Ioo 0 (T r),
          relativePosition μ ((φ u (S r) : LeftEnergyState μ c) : Phase) 1 < 0) ∧
        relativePosition μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase) 1 < 0 ∧
        StrictMonoOn
          (fun u : ℝ => relativePosition μ ((φ u (S r) : LeftEnergyState μ c) : Phase) 0)
          (Set.Icc 0 (T r)) ∧
        relativePosition μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase) 0 = 0 ∧
        0 < jacobiVelocity
          (leviCivitaToJacobi μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) 0 := by
  set G : ℝ → Prop := fun r => ∃ x : LeftEnergyState μ c,
    (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ with hG
  have hopen : ∀ r₀ > 0, G r₀ → ∃ δ > 0, ∀ r : ℝ, |r - r₀| < δ → G r := by
    rintro r₀ hr₀ ⟨x₀, hx₀, τ₀, harc⟩
    obtain ⟨δ, hδ, h⟩ := birkhoff_far_arc_continuity μ c hμ0 hμ1 hc φ hφ r₀ hr₀ x₀ τ₀ hx₀ harc 1
      one_pos
    exact ⟨δ, hδ, fun r hr => by
      obtain ⟨x, hx, τ, hτ, -⟩ := h r hr
      exact ⟨x, hx, τ, hτ⟩⟩
  obtain ⟨ε, hε, hεG, hlim0⟩ := birkhoff_far_arc_small μ c hμ0 hμ1 hc φ hφ
  have hbad1 : ¬ G 1 := by
    rintro ⟨x, hx, -⟩
    obtain ⟨ρ, hρ, hbound⟩ := left_component_position_radius_lt_one μ c hμ0 hμ1 hc
    have := hbound x x.2
    rw [hx] at this
    simp [leviCivitaPosition, farShootingStart] at this
    nlinarith
  obtain ⟨b, hb, hgood, hbadb⟩ := first_bad_parameter G hopen ⟨ε, hε, hεG⟩ 1 one_pos hbad1
  obtain ⟨E, hEcase⟩ := birkhoff_far_arc_end_rest μ c hμ0 hμ1 hc φ hφ b hb hgood hbadb
  have : Nonempty (LeftEnergyState μ c) :=
    ⟨⟨_, leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1⟩⟩
  set S : ℝ → LeftEnergyState μ c := fun r => Classical.epsilon (fun x : LeftEnergyState μ c =>
    (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ) with hS
  set T : ℝ → ℝ := fun r => Classical.epsilon (fun τ : ℝ => IsFarShootingArc φ (S r) τ) with hT
  have hST : ∀ r, G r → (S r : Phase) = farShootingStart μ c r ∧ IsFarShootingArc φ (S r) (T r) := by
    intro r hr
    have h1 := Classical.epsilon_spec (p := fun x : LeftEnergyState μ c =>
      (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ) hr
    exact ⟨h1.1, Classical.epsilon_spec (p := fun τ : ℝ => IsFarShootingArc φ (S r) τ) h1.2⟩
  have hid : ∀ r, G r → ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
      (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → x = S r ∧ τ = T r := by
    intro r hr x τ hx harc
    obtain ⟨h1, h2⟩ := hST r hr
    have hxS : x = S r := Subtype.ext (hx.trans h1.symm)
    subst hxS
    exact ⟨rfl, far_arc_unique μ c φ hφ _ τ (T r) harc h2⟩
  refine ⟨b, hb, E, S, T, ?_, ?_, ?_, ?_⟩
  · intro r₀ hr₀
    rw [Metric.continuousWithinAt_iff]
    intro e he
    obtain ⟨h1, h2⟩ := hST r₀ (hgood r₀ hr₀)
    obtain ⟨δ, hδ, h⟩ := birkhoff_far_arc_continuity μ c hμ0 hμ1 hc φ hφ r₀ hr₀.1 (S r₀) (T r₀)
      h1 h2 e he
    refine ⟨δ, hδ, fun r hr hdist => ?_⟩
    obtain ⟨x, hx, τ, harc, hd⟩ := h r (by rwa [Real.dist_eq] at hdist)
    obtain ⟨rfl, rfl⟩ := hid r (hgood r hr) x τ hx harc
    exact hd
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ, hδ, h⟩ := hlim0 e he
    refine ⟨min δ ε, lt_min hδ hε, fun r hr hdist => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hr] at hdist
    have hrε : r < ε := lt_of_lt_of_le hdist (min_le_right _ _)
    obtain ⟨h1, h2⟩ := hST r (hεG r ⟨hr, hrε⟩)
    exact h r ⟨hr, lt_of_lt_of_le hdist (min_le_left _ _)⟩ (S r) (T r) h1 h2
  · rcases hEcase with ⟨hE, hlimb⟩ | ⟨hE2, hEb, hlimb⟩
    · refine Or.inl ⟨hE, ?_⟩
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro e he
      obtain ⟨δ, hδ, h⟩ := hlimb e he
      refine ⟨min δ b, lt_min hδ hb, fun r hr hdist => ?_⟩
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by simpa using hr)] at hdist
      have hr0 : 0 < r := by linarith [min_le_right δ b]
      obtain ⟨h1, h2⟩ := hST r (hgood r ⟨hr0, hr⟩)
      exact h r ⟨by linarith [min_le_left δ b], hr⟩ (S r) (T r) h1 h2
    · refine Or.inr ⟨hE2, hEb, ?_⟩
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro e he
      obtain ⟨δ, hδ, h⟩ := hlimb e he
      refine ⟨min δ b, lt_min hδ hb, fun r hr hdist => ?_⟩
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by simpa using hr)] at hdist
      have hr0 : 0 < r := by linarith [min_le_right δ b]
      obtain ⟨h1, h2⟩ := hST r (hgood r ⟨hr0, hr⟩)
      rw [Real.dist_eq]
      exact h r ⟨by linarith [min_le_left δ b], hr⟩ (S r) (T r) h1 h2
  · intro r hr
    obtain ⟨h1, h2⟩ := hST r (hgood r hr)
    obtain ⟨c0, c1, c3⟩ := farStart_coords μ c r
    refine ⟨by rw [h1]; exact c0, by rw [h1]; exact c3, by rw [h1, c1]; exact hr.1.ne', h2.1,
      h2.2.1, h2.2.2.1, far_arc_mono μ c φ hφ _ _ h2, h2.2.2.2.1,
      h2.2.2.2.2 _ ⟨h2.1, le_refl _⟩⟩

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ b : ℝ, 0 < b ∧ ∃ E : ℝ × ℝ, ∃ S : ℝ → LeftEnergyState μ c, ∃ T : ℝ → ℝ,
      ContinuousOn (fun r : ℝ =>
        shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) (Set.Ioo 0 b) ∧
      Filter.Tendsto (fun r : ℝ =>
        shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(Real.sqrt 2 / 2), 0)) ∧
      (((((E.1 = -1 ∨ E.1 = 1) ∧ 0 < E.2) ∨ (E.2 = 0 ∧ Real.sqrt 2 / 2 < E.1)) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin b (Set.Iio b)) (nhds E)) ∨
       (0 < E.2 ∧
        (∀ s : LeftEnergyState μ c, relativePosition μ (s : Phase) 0 = 0 →
          relativePosition μ (s : Phase) 1 < 0 →
          0 < jacobiVelocity (leviCivitaToJacobi μ (s : Phase)) 0 →
          -relativePosition μ (s : Phase) 1 < E.2) ∧
        Filter.Tendsto (fun r : ℝ =>
          (shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)).2)
          (nhdsWithin b (Set.Iio b)) (nhds E.2))) ∧
      ∀ r ∈ Set.Ioo 0 b,
        ((S r : LeftEnergyState μ c) : Phase) 0 = 0 ∧
        ((S r : LeftEnergyState μ c) : Phase) 3 = 0 ∧
        ((S r : LeftEnergyState μ c) : Phase) 1 ≠ 0 ∧
        0 < T r ∧
        (∀ u ∈ Set.Ioo 0 (T r),
          relativePosition μ ((φ u (S r) : LeftEnergyState μ c) : Phase) 1 < 0) ∧
        relativePosition μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase) 1 < 0 ∧
        StrictMonoOn
          (fun u : ℝ => relativePosition μ ((φ u (S r) : LeftEnergyState μ c) : Phase) 0)
          (Set.Icc 0 (T r)) ∧
        relativePosition μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase) 0 = 0 ∧
        0 < jacobiVelocity
          (leviCivitaToJacobi μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) 0 :=
  far_crossing_curve_rest μ c hμ0 hμ1 hc φ hφ
