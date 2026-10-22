-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_arc_end_rest
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T19:02:44.188641+00:00
-- url     : https://prove2.me/submissions/f83dfa9a-e9b4-4cf7-a291-23295e0cf084

import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_limit_end
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_collision_strict
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_limit_rest
import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffShootingCoordinates
import Theorems.Thm_BirkhoffGlobalSection_partial_derivative_eq_update_deriv
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_circle_hamiltonian_lower_bound
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_realizes_first_critical_value
import Theorems.Thm_BirkhoffGlobalSection_leftCollisionPoint_mem_leftEnergyComponent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_disk_vertical_tidal_factor
import Definitions.Def_BirkhoffShootingArcs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

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

/-- The selected component projects into the open disk bounded by the inner Lagrange circle. -/
lemma component_in_L1_disk (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (L : Phase) (hL : IsInnerLagrangePoint μ L)
    (hLval : jacobiHamiltonian μ L = firstCriticalValue μ) :
    ∀ s ∈ leftEnergyComponent μ c,
      (leviCivitaPosition μ s 0 + μ) ^ 2 + (leviCivitaPosition μ s 1) ^ 2 < (L 0 + μ) ^ 2 := by
  intro s hs
  by_contra hge
  push Not at hge
  set f : Phase → ℝ := fun s => (leviCivitaPosition μ s 0 + μ) ^ 2 + (leviCivitaPosition μ s 1) ^ 2
  have hf : Continuous f := by
    simp only [f, leviCivitaPosition]; fun_prop
  have hpre : IsPreconnected (leftEnergyComponent μ c) := isPreconnected_connectedComponentIn
  have h0 := leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1
  have hf0 : f (leftCollisionPoint μ) = 0 := by
    simp [f, leviCivitaPosition, leftCollisionPoint]
  have hmem : (L 0 + μ) ^ 2 ∈ Icc (f (leftCollisionPoint μ)) (f s) :=
    ⟨by rw [hf0]; positivity, hge⟩
  obtain ⟨s', hs', hfs'⟩ := hpre.intermediate_value h0 hs hf.continuousOn hmem
  have hbound := inner_lagrange_circle_hamiltonian_lower_bound μ hμ0 hμ1 L hL s' hfs'
  have hK : leviCivitaHamiltonian μ c s' = 0 := (connectedComponentIn_subset _ _ hs').1
  have hK0 : leviCivitaHamiltonian μ 0 s' = -c * zNormSq s' := by
    have : leviCivitaHamiltonian μ c s' - leviCivitaHamiltonian μ 0 s' = c * zNormSq s' := by
      unfold leviCivitaHamiltonian; ring
    linarith
  have hLpos : 0 < L 0 + μ := by linarith [hL.2.2.1]
  have hP : 0 < zNormSq s' := by
    have e : f s' = (2 * zNormSq s') ^ 2 := by
      simp only [f, leviCivitaPosition, zNormSq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]; ring
    have hz : 0 ≤ zNormSq s' := by unfold zNormSq; positivity
    rcases hz.lt_or_eq with h | h
    · exact h
    · exfalso; rw [hfs', ← h] at e; simp at e; linarith
  rw [hK0] at hbound
  have : jacobiHamiltonian μ L ≤ -c := by
    have := mul_le_mul_of_nonneg_left (le_refl (1:ℝ)) hP.le
    nlinarith
  unfold belowFirstCriticalValue at hc
  linarith

noncomputable def Vx (s : Phase) : ℝ := (s 2 * s 0 - s 3 * s 1) / (s 0 ^ 2 + s 1 ^ 2) - 4 * s 0 * s 1

noncomputable def Vy (μ : ℝ) (s : Phase) : ℝ :=
  (s 2 * s 1 + s 3 * s 0) / (s 0 ^ 2 + s 1 ^ 2) + 2 * (s 0 ^ 2 - s 1 ^ 2) - μ

lemma jv_eq (μ : ℝ) (s : Phase) :
    jacobiVelocity (leviCivitaToJacobi μ s) 0 = Vx s ∧
      jacobiVelocity (leviCivitaToJacobi μ s) 1 = Vy μ s := by
  constructor <;>
    simp [jacobiVelocity, leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum, zNormSq, Vx, Vy] <;>
    ring

lemma relPos_eq (μ : ℝ) (s : Phase) :
    relativePosition μ s 0 = 2 * (s 0 ^ 2 - s 1 ^ 2) ∧ relativePosition μ s 1 = 4 * s 0 * s 1 := by
  simp [relativePosition, leviCivitaPosition]

-- ===== Solutions.CM3 =====
noncomputable def farR (μ c r : ℝ) : ℝ :=
  (1 - μ) + r ^ 2 * ((2 * r ^ 2 + μ) ^ 2 + 2 * μ / (1 + 2 * r ^ 2) - 2 * c)

lemma farR_continuous (μ c : ℝ) : Continuous (farR μ c) := by
  unfold farR
  have : ∀ r : ℝ, 1 + 2 * r ^ 2 ≠ 0 := fun r => by positivity
  fun_prop (disch := exact this _)

lemma farStart_continuous (μ c : ℝ) : Continuous (farShootingStart μ c) := by
  have hR := farR_continuous μ c
  have e : farShootingStart μ c = fun r =>
      ![0, r, r * (2 * r ^ 2 + μ) - Real.sqrt (farR μ c r), 0] := rfl
  rw [e]
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_id
  · exact (by fun_prop : Continuous fun r : ℝ => r * (2 * r ^ 2 + μ)).sub hR.sqrt
  · exact continuous_const

-- ===== Solutions.Abstract =====
section Abstract

variable {X : Type*} [TopologicalSpace X]

-- ===== Solutions.CM5 =====
lemma cont_Vx (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0) : ContinuousAt Vx s := by
  unfold Vx; fun_prop (disch := exact hP)

lemma cont_Vy (μ : ℝ) (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0) : ContinuousAt (Vy μ) s := by
  unfold Vy; fun_prop (disch := exact hP)

lemma coords_eq (μ : ℝ) : shootingCoordinates μ = fun s : Phase =>
    (Vy μ s / Real.sqrt (Vx s ^ 2 + Vy μ s ^ 2), -(4 * s 0 * s 1)) := by
  funext s
  simp only [shootingCoordinates, (jv_eq μ s).1, (jv_eq μ s).2, (relPos_eq μ s).2]

-- ===== Solutions.CM8 =====
noncomputable def Xa (μ : ℝ) (s : Phase) : ℝ := s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1 - μ * s 1
noncomputable def Xb (μ : ℝ) (s : Phase) : ℝ := s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0 - μ * s 0
noncomputable def Xp (μ c : ℝ) (s : Phase) : ℝ :=
  -(2 * c * s 0 + 4 * s 0 * (s 0 * s 3 - s 1 * s 2) + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 3
    - μ * s 3 - μ * (2 * s 0 / Real.sqrt (secondCollisionDistanceSq s)
      - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 0 * (2 * (s 0 ^ 2 + s 1 ^ 2) - 1) /
        Real.sqrt (secondCollisionDistanceSq s) ^ 3))
noncomputable def Xq (μ c : ℝ) (s : Phase) : ℝ :=
  -(2 * c * s 1 + 4 * s 1 * (s 0 * s 3 - s 1 * s 2) - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 2
    - μ * s 2 - μ * (2 * s 1 / Real.sqrt (secondCollisionDistanceSq s)
      - 4 * (s 0 ^ 2 + s 1 ^ 2) * s 1 * (2 * (s 0 ^ 2 + s 1 ^ 2) + 1) /
        Real.sqrt (secondCollisionDistanceSq s) ^ 3))

lemma flow_coords' (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 0)
        (Xa μ ((φ t x : LeftEnergyState μ c) : Phase)) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 1)
        (Xb μ ((φ t x : LeftEnergyState μ c) : Phase)) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 2)
        (Xp μ c ((φ t x : LeftEnergyState μ c) : Phase)) t ∧
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase) 3)
        (Xq μ c ((φ t x : LeftEnergyState μ c) : Phase)) t :=
  flow_coords μ c φ hφ x t

-- ===== Solutions.CM11 =====
noncomputable def Gfar (μ α p q : ℝ) : ℝ :=
  (p - q - 2 * α * μ) / Real.sqrt ((8 * α ^ 3 - p - q) ^ 2 + (p - q - 2 * α * μ) ^ 2)

lemma coords_far_cross (μ : ℝ) (s : Phase) (α : ℝ) (hα : 0 < α) (h0 : s 0 = -α) (h1 : s 1 = α) :
    shootingCoordinates μ s = (Gfar μ α (s 2) (s 3), 4 * α ^ 2) := by
  rw [coords_eq]
  simp only [Vx, Vy, Gfar, h0, h1]
  congr 1
  · have e1 : (s 2 * -α - s 3 * α) / ((-α) ^ 2 + α ^ 2) - 4 * -α * α =
        (8 * α ^ 3 - s 2 - s 3) / (2 * α) := by field_simp; ring
    have e2 : (s 2 * α + s 3 * -α) / ((-α) ^ 2 + α ^ 2) + 2 * ((-α) ^ 2 - α ^ 2) - μ =
        (s 2 - s 3 - 2 * α * μ) / (2 * α) := by field_simp; ring
    rw [e1, e2, div_pow, div_pow, ← add_div, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by positivity), div_div_div_cancel_right₀ (by positivity)]
  · ring

-- ===== Solutions.CM29 =====
/-! Birkhoff's identity (59): the angular momentum about the primary along far arcs. -/

-- ===== Solutions.CM34 =====
/-- The Jacobi potential restricted to the vertical line through the large primary,
at depth `y` below the axis. -/
noncomputable def hillF (μ y : ℝ) : ℝ :=
  (μ ^ 2 + y ^ 2) / 2 + (1 - μ) / y + μ / Real.sqrt (1 + y ^ 2)

lemma energy_general (μ c : ℝ) (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0)
    (hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0) :
    Vx s ^ 2 + Vy μ s ^ 2 = (2 * (s 0 ^ 2 - s 1 ^ 2) - μ) ^ 2 + (4 * s 0 * s 1) ^ 2 +
      (1 - μ) / (s 0 ^ 2 + s 1 ^ 2) + 2 * μ / Real.sqrt (secondCollisionDistanceSq s) - 2 * c +
      2 * leviCivitaHamiltonian μ c s / (s 0 ^ 2 + s 1 ^ 2) := by
  unfold Vx Vy leviCivitaHamiltonian wNormSq zNormSq
  set N := Real.sqrt (secondCollisionDistanceSq s)
  field_simp
  ring

/-- Energy on the vertical line: `|v|² = 2 (Ω - c)`. -/
lemma energy_line (μ c : ℝ) (s : Phase) (hs : s ∈ leftEnergyComponent μ c)
    (hX : 2 * (s 0 ^ 2 - s 1 ^ 2) = 0) (hY : 4 * s 0 * s 1 < 0) :
    Vx s ^ 2 + Vy μ s ^ 2 = 2 * (hillF μ (-(4 * s 0 * s 1)) - c) := by
  have hK : leviCivitaHamiltonian μ c s = 0 := (connectedComponentIn_subset _ _ hs).1
  have h01 : s 0 ^ 2 = s 1 ^ 2 := by linarith
  have hs0 : s 0 ≠ 0 := by rintro h; rw [h] at hY; simp at hY
  have hP : 0 < s 0 ^ 2 + s 1 ^ 2 := by positivity
  have hD : secondCollisionDistanceSq s = 1 + (4 * s 0 * s 1) ^ 2 := by
    unfold secondCollisionDistanceSq; rw [show s 0 ^ 2 - s 1 ^ 2 = 0 by linarith]; ring
  have hN : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := by
    rw [hD]; positivity
  rw [energy_general μ c s hP.ne' hN, hK, hD]
  set y := -(4 * s 0 * s 1) with hy
  have hy0 : 0 < y := by linarith
  have hyP : y = 2 * (s 0 ^ 2 + s 1 ^ 2) := by
    have e : y ^ 2 = (2 * (s 0 ^ 2 + s 1 ^ 2)) ^ 2 := by
      rw [hy]; nlinarith [h01]
    have := (sq_eq_sq₀ hy0.le (by positivity)).1 e
    exact this
  have e2 : (4 * s 0 * s 1) ^ 2 = y ^ 2 := by rw [hy]; ring
  rw [e2, show 2 * (s 0 ^ 2 - s 1 ^ 2) = 0 by linarith]
  unfold hillF
  have hPe : s 0 ^ 2 + s 1 ^ 2 = y / 2 := by linarith
  rw [hPe]
  field_simp
  ring

lemma hill_hasDerivAt (μ y : ℝ) (hy : 0 < y) :
    HasDerivAt (hillF μ) (y - (1 - μ) / y ^ 2 - μ * y / Real.sqrt (1 + y ^ 2) ^ 3) y := by
  have hq : (0:ℝ) < 1 + y ^ 2 := by positivity
  have hsq : Real.sqrt (1 + y ^ 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have h1 : HasDerivAt (fun y : ℝ => (μ ^ 2 + y ^ 2) / 2) y y :=
    (((hasDerivAt_pow 2 y).const_add (μ ^ 2)).div_const 2).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun y : ℝ => (1 - μ) / y) (-((1 - μ) / y ^ 2)) y :=
    ((hasDerivAt_const y (1 - μ)).div (hasDerivAt_id' y) hy.ne').congr_deriv (by ring)
  have hg : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      ((2 * y) / (2 * Real.sqrt (1 + y ^ 2))) y :=
    (((hasDerivAt_pow 2 y).const_add 1).sqrt hq.ne').congr_deriv (by norm_num)
  have h3 : HasDerivAt (fun y : ℝ => μ / Real.sqrt (1 + y ^ 2))
      (-(μ * y / Real.sqrt (1 + y ^ 2) ^ 3)) y :=
    ((hasDerivAt_const y μ).div hg hsq).congr_deriv (by field_simp; ring)
  unfold hillF
  exact ((h1.add h2).add h3).congr_deriv (by ring)

lemma hill_anti (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase) (hL : IsInnerLagrangePoint μ L) :
    StrictAntiOn (hillF μ) (Ioo 0 (L 0 + μ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro y hy; exact (hill_hasDerivAt μ y hy.1).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(hill_hasDerivAt μ y hy.1).deriv]
    have hpos : 0 < (-μ + μ) ^ 2 + y ^ 2 := by
      have := hy.1; rw [show -μ + μ = 0 by ring]; positivity
    have hr : (-μ + μ) ^ 2 + y ^ 2 < (L 0 + μ) ^ 2 := by
      rw [show -μ + μ = 0 by ring]
      nlinarith [hy.1, hy.2]
    have hT := inner_lagrange_disk_vertical_tidal_factor μ hμ0 hμ1 L hL (-μ) y hpos hr
    rw [show (-μ + μ) ^ 2 + y ^ 2 = y ^ 2 by ring, Real.sqrt_sq hy.1.le,
      show (-μ - 1 + μ) ^ 2 + y ^ 2 = 1 + y ^ 2 by ring] at hT
    have hy0 := hy.1
    have e : y - (1 - μ) / y ^ 2 - μ * y / Real.sqrt (1 + y ^ 2) ^ 3 =
        y * (1 - ((1 - μ) / y ^ 3 + μ / Real.sqrt (1 + y ^ 2) ^ 3)) := by
      field_simp
      ring
    rw [e]
    exact mul_neg_of_pos_of_neg hy0 (by linarith)

/-- Hill-depth bound: a moving state on the vertical line below the axis lies strictly above
a state of rest on the same line. -/
lemma hill_depth (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (s r : Phase) (hs : s ∈ leftEnergyComponent μ c) (hr : r ∈ leftEnergyComponent μ c)
    (hsX : 2 * (s 0 ^ 2 - s 1 ^ 2) = 0) (hsY : 4 * s 0 * s 1 < 0)
    (hrX : 2 * (r 0 ^ 2 - r 1 ^ 2) = 0) (hrY : 4 * r 0 * r 1 < 0)
    (hrv : Vx r = 0 ∧ Vy μ r = 0) (hsv : 0 < Vx s ^ 2 + Vy μ s ^ 2) :
    -(4 * s 0 * s 1) < -(4 * r 0 * r 1) := by
  obtain ⟨L, hL, hLval⟩ := inner_lagrange_realizes_first_critical_value μ hμ0 hμ1
  have hdisk := component_in_L1_disk μ c hμ0 hμ1 hc L hL hLval
  have hLpos : 0 < L 0 + μ := by linarith [hL.2.2.1]
  have hin : ∀ q ∈ leftEnergyComponent μ c, 2 * (q 0 ^ 2 - q 1 ^ 2) = 0 → 4 * q 0 * q 1 < 0 →
      -(4 * q 0 * q 1) ∈ Ioo 0 (L 0 + μ) := by
    intro q hq hX hY
    have h := hdisk q hq
    simp only [leviCivitaPosition, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at h
    rw [show 2 * (q 0 ^ 2 - q 1 ^ 2) - μ + μ = 0 by linarith] at h
    refine ⟨by linarith, ?_⟩
    nlinarith
  have hEs := energy_line μ c s hs hsX hsY
  have hEr := energy_line μ c r hr hrX hrY
  rw [hrv.1, hrv.2] at hEr
  by_contra hge
  push Not at hge
  have hle := (hill_anti μ hμ0 hμ1 L hL).antitoneOn (hin r hr hrX hrY) (hin s hs hsX hsY) hge
  linarith

-- ===== Solutions.CM18 =====
/-- The crossing state of a far arc lies on the diagonal `z = (-α, α)` with `α > 0`. -/
lemma far_cross_state (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (τ : ℝ)
    (hx1 : 0 < (x : Phase) 1) (harc : IsFarShootingArc φ x τ) :
    0 < ((φ τ x : LeftEnergyState μ c) : Phase) 1 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 0 = -((φ τ x : LeftEnergyState μ c) : Phase) 1 := by
  obtain ⟨hτ, hy, hend, hcross, -⟩ := harc
  have hpos : 0 < ((φ τ x : LeftEnergyState μ c) : Phase) 1 := by
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn (fun u => ((φ u x : LeftEnergyState μ c) : Phase) 1) (Icc 0 τ) :=
      fun u _ => ((flow_coords' μ c φ hφ x u).2.1).continuousAt.continuousWithinAt
    have h0 : ((φ 0 x : LeftEnergyState μ c) : Phase) 1 = (x : Phase) 1 := by simp
    have hmem : (0:ℝ) ∈ Icc ((fun u => ((φ u x : LeftEnergyState μ c) : Phase) 1) τ)
        ((fun u => ((φ u x : LeftEnergyState μ c) : Phase) 1) 0) :=
      ⟨hneg, by simp only; rw [h0]; exact hx1.le⟩
    obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc' hτ.le hcont hmem
    simp only at hu0
    have hu' : u ≠ 0 := by rintro rfl; rw [h0] at hu0; linarith
    rcases eq_or_lt_of_le hu.2 with h | h
    · subst h
      have := hend; rw [(relPos_eq μ _).2, hu0] at this; simp at this
    · have := hy u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu'), h⟩
      rw [(relPos_eq μ _).2, hu0] at this; simp at this
  refine ⟨hpos, ?_⟩
  have hy' := hend; rw [(relPos_eq μ _).2] at hy'
  have hxr := hcross; rw [(relPos_eq μ _).1] at hxr
  have h0 : ((φ τ x : LeftEnergyState μ c) : Phase) 0 < 0 := by
    by_contra h; push Not at h; nlinarith
  have e : (((φ τ x : LeftEnergyState μ c) : Phase) 0 - ((φ τ x : LeftEnergyState μ c) : Phase) 1) *
      (((φ τ x : LeftEnergyState μ c) : Phase) 0 + ((φ τ x : LeftEnergyState μ c) : Phase) 1) = 0 := by
    linarith [show (((φ τ x : LeftEnergyState μ c) : Phase) 0 - ((φ τ x : LeftEnergyState μ c) : Phase) 1) *
      (((φ τ x : LeftEnergyState μ c) : Phase) 0 + ((φ τ x : LeftEnergyState μ c) : Phase) 1) =
      ((φ τ x : LeftEnergyState μ c) : Phase) 0 ^ 2 - ((φ τ x : LeftEnergyState μ c) : Phase) 1 ^ 2 by ring]
  rcases mul_eq_zero.1 e with h | h
  · linarith
  · linarith

/-- The far crossing-coordinate value at a collision velocity with `w₀ > 0 > w₁`. -/
lemma Gfar_collision_bound (μ w0 w1 : ℝ) (h0 : 0 < w0) (h1 : w1 < 0) :
    Real.sqrt 2 / 2 < Gfar μ 0 w0 w1 := by
  have e : Gfar μ 0 w0 w1 = (w0 - w1) / Real.sqrt ((w0 + w1) ^ 2 + (w0 - w1) ^ 2) := by
    unfold Gfar; congr 1 <;> ring_nf
  rw [e]
  set X := (w0 + w1) ^ 2 + (w0 - w1) ^ 2 with hX
  have hXpos : 0 < X := by
    have : 0 < (w0 - w1) ^ 2 := by nlinarith
    rw [hX]; nlinarith [sq_nonneg (w0 + w1)]
  set D := Real.sqrt X with hD
  have hDpos : 0 < D := Real.sqrt_pos.2 hXpos
  have hD2 : D ^ 2 = X := Real.sq_sqrt hXpos.le
  have hs2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have hs0 : 0 < Real.sqrt 2 / 2 := by positivity
  set a := (w0 - w1) / D with ha
  have haD : a * D = w0 - w1 := by rw [ha]; field_simp
  have hpos : 0 < a := div_pos (by linarith) hDpos
  have hsq : a ^ 2 * X = (w0 - w1) ^ 2 := by rw [← hD2, ← mul_pow, haD]
  have h2 : 1 / 2 < a ^ 2 := by
    by_contra h; push Not at h
    have : a ^ 2 * X ≤ 1 / 2 * X := mul_le_mul_of_nonneg_right h hXpos.le
    nlinarith [mul_pos h0 (neg_pos.2 h1)]
  nlinarith

lemma cont_coords' (μ : ℝ) (s : Phase) (hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0) (hv : Vy μ s ≠ 0) :
    ContinuousAt (shootingCoordinates μ) s := by
  rw [coords_eq]
  have hx := cont_Vx s hP
  have hy := cont_Vy μ s hP
  have hsq : Real.sqrt (Vx s ^ 2 + Vy μ s ^ 2) ≠ 0 := by
    apply (Real.sqrt_pos.2 _).ne'
    have : 0 < Vy μ s ^ 2 := by positivity
    positivity
  apply ContinuousAt.prodMk
  · exact hy.div ((hx.pow 2).add (hy.pow 2)).sqrt hsq
  · fun_prop

/-- Convergence of far crossing coordinates, given a formula continuous at the limit state. -/
lemma far_conv (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c)) (b : ℝ) (hb : 0 < b)
    (xb : LeftEnergyState μ c) (hxb : (xb : Phase) = farShootingStart μ c b) (T : ℝ)
    (hconv : ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → |τ - T| < η)
    (H : Phase → ℝ × ℝ) (hH : ContinuousAt H ((φ T xb : LeftEnergyState μ c) : Phase))
    (hHc : ∀ r, 0 < r → ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
      (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
      shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase) =
        H ((φ τ x : LeftEnergyState μ c) : Phase)) :
    ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
          dist (shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase))
            (H ((φ T xb : LeftEnergyState μ c) : Phase)) < η := by
  intro η hη
  set F : ℝ × LeftEnergyState μ c → Phase := fun p => ((φ p.1 p.2 : LeftEnergyState μ c) : Phase)
    with hF
  have hFc : Continuous F := continuous_subtype_val.comp φ.cont'
  have hHF : ContinuousAt (H ∘ F) (T, xb) :=
    ContinuousAt.comp (g := H) (f := F) (x := (T, xb)) hH hFc.continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hHF η hη
  obtain ⟨δ1, hδ1, hN⟩ :=
    Metric.continuousAt_iff.1
      ((farStart_continuous μ c).continuousAt : ContinuousAt (farShootingStart μ c) b) ε hε
  obtain ⟨δ2, hδ2, hτ⟩ := hconv ε hε
  refine ⟨min b (min δ1 δ2), lt_min hb (lt_min hδ1 hδ2), fun r hr x τ hx harc => ?_⟩
  have hr0 : 0 < r := by linarith [hr.1, min_le_left b (min δ1 δ2)]
  have hrδ1 : dist r b < δ1 := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hr.2])]
    linarith [hr.1, min_le_left δ1 δ2, min_le_right b (min δ1 δ2)]
  have hrδ2 : r ∈ Ioo (b - δ2) b :=
    ⟨by linarith [hr.1, min_le_right δ1 δ2, min_le_right b (min δ1 δ2)], hr.2⟩
  rw [hHc r hr0 x τ hx harc]
  have := @hball (τ, x) (by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq]; exact hτ r hrδ2 x τ hx harc
    · rw [Subtype.dist_eq, hx, hxb]; exact hN hrδ1)
  exact this

-- ===== Solutions.CM35 =====
/-- Convergence of a continuous observable at the far crossing states. -/
lemma far_conv_real (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c)) (b : ℝ) (hb : 0 < b)
    (xb : LeftEnergyState μ c) (hxb : (xb : Phase) = farShootingStart μ c b) (T : ℝ)
    (hconv : ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → |τ - T| < η)
    (H : Phase → ℝ) (hH : Continuous H) :
    ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
          |H ((φ τ x : LeftEnergyState μ c) : Phase) - H ((φ T xb : LeftEnergyState μ c) : Phase)| < η := by
  have := far_conv μ c φ b hb xb hxb T hconv (fun s => (H s, (0:ℝ)))
    (by fun_prop)
  intro η hη
  set F : ℝ × LeftEnergyState μ c → Phase := fun p => ((φ p.1 p.2 : LeftEnergyState μ c) : Phase)
    with hF
  have hFc : Continuous F := continuous_subtype_val.comp φ.cont'
  have hHF : ContinuousAt (H ∘ F) (T, xb) := (hH.comp hFc).continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hHF η hη
  obtain ⟨δ1, hδ1, hN⟩ :=
    Metric.continuousAt_iff.1
      ((farStart_continuous μ c).continuousAt : ContinuousAt (farShootingStart μ c) b) ε hε
  obtain ⟨δ2, hδ2, hτ⟩ := hconv ε hε
  refine ⟨min b (min δ1 δ2), lt_min hb (lt_min hδ1 hδ2), fun r hr x τ hx harc => ?_⟩
  have hrδ1 : dist r b < δ1 := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hr.2])]
    linarith [hr.1, min_le_left δ1 δ2, min_le_right b (min δ1 δ2)]
  have hrδ2 : r ∈ Ioo (b - δ2) b :=
    ⟨by linarith [hr.1, min_le_right δ1 δ2, min_le_right b (min δ1 δ2)], hr.2⟩
  have := @hball (τ, x) (by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq]; exact hτ r hrδ2 x τ hx harc
    · rw [Subtype.dist_eq, hx, hxb]; exact hN hrδ1)
  rw [Real.dist_eq] at this
  exact this

set_option maxHeartbeats 2000000 in
theorem far_arc_end_rest (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (b : ℝ) (hb : 0 < b)
    (hgood : ∀ r ∈ Set.Ioo 0 b, ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)
    (hbad : ¬ (∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c b ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)) :
    ∃ E : ℝ × ℝ,
      ((((E.1 = -1 ∨ E.1 = 1) ∧ 0 < E.2) ∨ (E.2 = 0 ∧ Real.sqrt 2 / 2 < E.1)) ∧
        ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
          (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
            dist (shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase)) E < η) ∨
      (0 < E.2 ∧
        (∀ s : LeftEnergyState μ c, relativePosition μ (s : Phase) 0 = 0 →
          relativePosition μ (s : Phase) 1 < 0 →
          0 < jacobiVelocity (leviCivitaToJacobi μ (s : Phase)) 0 →
          -relativePosition μ (s : Phase) 1 < E.2) ∧
        ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
          (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
            |(shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase)).2 - E.2| < η) := by
  obtain ⟨xb, hxb, hv, T, hT, hcl, hvx, hP, hX, hY, hVxT, hconv⟩ :=
    birkhoff_far_arc_limit_rest μ c hμ0 hμ1 hc φ hφ b hb hgood hbad
  have hno : ¬ ∃ τ, IsFarShootingArc φ xb τ := fun h => hbad ⟨xb, hxb, h⟩
  have hb0 : (xb : Phase) 0 = 0 := by rw [hxb]; simp [farShootingStart]
  have hb1 : (xb : Phase) 1 = b := by rw [hxb]; simp [farShootingStart]
  obtain ⟨hy, hcase⟩ := birkhoff_far_limit_end μ c hμ0 hμ1 hc φ hφ xb T hT hb0 (by rw [hb1]; exact hb)
    hv hcl hvx hP hX hY hVxT hno
  set s₀ : Phase := ((φ T xb : LeftEnergyState μ c) : Phase) with hs₀
  rcases hcase with ⟨hc0, hc1⟩ | ⟨hyT, hvx0⟩
  · -- collision end
    obtain ⟨hw0, hw1⟩ := birkhoff_far_collision_strict μ c hμ0 hμ1 hc φ hφ xb T hT
      (by rw [hb1]; exact hb) hy hvx hc0 hc1
    set G : Phase → ℝ × ℝ := fun s => (Gfar μ (s 1) (s 2) (s 3), 4 * s 1 ^ 2) with hG
    have hGc : ContinuousAt G s₀ := by
      have hden : Real.sqrt ((8 * s₀ 1 ^ 3 - s₀ 2 - s₀ 3) ^ 2 + (s₀ 2 - s₀ 3 - 2 * s₀ 1 * μ) ^ 2) ≠ 0 := by
        apply (Real.sqrt_pos.2 _).ne'
        rw [hc1]
        have : 0 < (s₀ 2 - s₀ 3) ^ 2 := by
          have : 0 < s₀ 2 - s₀ 3 := by linarith
          positivity
        nlinarith [sq_nonneg (8 * (0:ℝ) ^ 3 - s₀ 2 - s₀ 3)]
      apply ContinuousAt.prodMk
      · unfold Gfar
        exact ContinuousAt.div (by fun_prop)
          ((by fun_prop : ContinuousAt (fun s : Phase => (8 * s 1 ^ 3 - s 2 - s 3) ^ 2 +
            (s 2 - s 3 - 2 * s 1 * μ) ^ 2) s₀).sqrt) hden
      · exact (continuous_const.mul ((continuous_apply 1).pow 2)).continuousAt
    have hGs₀ : G s₀ = (Gfar μ 0 (s₀ 2) (s₀ 3), 0) := by
      rw [show G s₀ = (Gfar μ (s₀ 1) (s₀ 2) (s₀ 3), 4 * s₀ 1 ^ 2) from rfl, hc1]; norm_num
    refine ⟨G s₀, Or.inl ⟨Or.inr ⟨by rw [hGs₀], by rw [hGs₀]; exact Gfar_collision_bound μ _ _ hw0 hw1⟩, ?_⟩⟩
    apply far_conv μ c φ b hb xb hxb T hconv G hGc
    intro r hr x τ hx harc
    have hx1 : 0 < (x : Phase) 1 := by rw [hx]; simp [farShootingStart]; exact hr
    obtain ⟨hcpos, hcdiag⟩ := far_cross_state μ c φ hφ x τ hx1 harc
    rw [coords_far_cross μ _ _ hcpos hcdiag rfl]
  have hy0 : 4 * s₀ 0 * s₀ 1 < 0 := by rw [← (relPos_eq μ _).2]; exact hyT
  have hX0 : 2 * (s₀ 0 ^ 2 - s₀ 1 ^ 2) = 0 := by rw [← (relPos_eq μ _).1]; exact hX
  rw [(jv_eq μ _).1] at hvx0
  by_cases hvy : Vy μ s₀ = 0
  · -- a state of rest on the vertical line
    refine ⟨(0, -relativePosition μ s₀ 1), Or.inr ⟨by simp only; linarith, ?_, ?_⟩⟩
    · intro s hsX hsY hsv
      simp only
      rw [(relPos_eq μ _).2, (relPos_eq μ _).2]
      rw [(relPos_eq μ _).1] at hsX
      rw [(relPos_eq μ _).2] at hsY
      rw [(jv_eq μ _).1] at hsv
      exact hill_depth μ c hμ0 hμ1 hc s s₀ s.2 (φ T xb).2 hsX hsY hX0 hy0 ⟨hvx0, hvy⟩
        (by positivity)
    · have := far_conv_real μ c φ b hb xb hxb T hconv (fun s => -relativePosition μ s 1)
        (by simp only [relativePosition, leviCivitaPosition]; fun_prop)
      intro η hη
      obtain ⟨δ, hδ, h⟩ := this η hη
      exact ⟨δ, hδ, fun r hr x τ hx harc => by
        have := h r hr x τ hx harc
        simpa [shootingCoordinates] using this⟩
  · -- a vertical tangency with nonzero velocity
    have hP' : s₀ 0 ^ 2 + s₀ 1 ^ 2 ≠ 0 := by
      have : s₀ 0 ≠ 0 := by rintro h; rw [h] at hy0; simp at hy0
      positivity
    refine ⟨shootingCoordinates μ s₀, Or.inl ⟨Or.inl ⟨?_, ?_⟩, ?_⟩⟩
    · rw [coords_eq]
      simp only
      rw [hvx0]
      rcases lt_or_gt_of_ne hvy with h | h
      · left
        rw [show (0:ℝ) ^ 2 + Vy μ s₀ ^ 2 = (-Vy μ s₀) ^ 2 by ring, Real.sqrt_sq (by linarith)]
        field_simp
      · right
        rw [show (0:ℝ) ^ 2 + Vy μ s₀ ^ 2 = Vy μ s₀ ^ 2 by ring, Real.sqrt_sq h.le]
        field_simp
    · rw [coords_eq]; simp only; linarith
    · exact far_conv μ c φ b hb xb hxb T hconv (shootingCoordinates μ) (cont_coords' μ s₀ hP' hvy)
        (fun _ _ _ _ _ _ => rfl)

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (b : ℝ) (hb : 0 < b)
    (hgood : ∀ r ∈ Set.Ioo 0 b, ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)
    (hbad : ¬ (∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c b ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)) :
    ∃ E : ℝ × ℝ,
      ((((E.1 = -1 ∨ E.1 = 1) ∧ 0 < E.2) ∨ (E.2 = 0 ∧ Real.sqrt 2 / 2 < E.1)) ∧
        ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
          (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
            dist (shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase)) E < η) ∨
      (0 < E.2 ∧
        (∀ s : LeftEnergyState μ c, relativePosition μ (s : Phase) 0 = 0 →
          relativePosition μ (s : Phase) 1 < 0 →
          0 < jacobiVelocity (leviCivitaToJacobi μ (s : Phase)) 0 →
          -relativePosition μ (s : Phase) 1 < E.2) ∧
        ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
          (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
            |(shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase)).2 - E.2| < η)
 :=
  far_arc_end_rest μ c hμ0 hμ1 hc φ hφ b hb hgood hbad
