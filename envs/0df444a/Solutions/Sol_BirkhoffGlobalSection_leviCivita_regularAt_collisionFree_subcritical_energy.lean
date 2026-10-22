-- Prove2me | solution 1 for BirkhoffGlobalSection.leviCivita_regularAt_collisionFree_subcritical_energy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T22:56:25.871751+00:00
-- url     : https://prove2.me/submissions/5fd1af2d-c170-422a-a398-5d1c890abf27

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_jacobi_collisionFree_differentiableAt
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_minimizes_critical_energy
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_point_exists
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

open BirkhoffGlobalSection Filter Topology

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (s : Phase)
    (hK : leviCivitaHamiltonian μ c s = 0)
    (hD : 0 < secondCollisionDistanceSq s)
    (hz : 0 < zNormSq s) :
    fderiv ℝ (leviCivitaHamiltonian μ c) s ≠ 0 := by
  intro hdK
  -- differentiability of the regularized Hamiltonian
  have hKdiff : DifferentiableAt ℝ (leviCivitaHamiltonian μ c) s := by
    have hDne : (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2 ≠ 0 := by
      have := hD.ne'; unfold secondCollisionDistanceSq at this; exact this
    have hSne : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) ≠ 0 :=
      (Real.sqrt_pos.2 (lt_of_le_of_ne (by positivity) (Ne.symm hDne))).ne'
    unfold leviCivitaHamiltonian zNormSq wNormSq secondCollisionDistanceSq
    fun_prop (disch := assumption)
  -- the Levi-Civita identity `K = |z|^2 (H + c)`
  have hident : ∀ y : Phase, 0 < zNormSq y → 0 < secondCollisionDistanceSq y →
      jacobiHamiltonian μ (leviCivitaToJacobi μ y) =
        leviCivitaHamiltonian μ c y / zNormSq y - c := by
    intro y hy hDy
    have hr1 : Real.sqrt ((2 * (y 0 ^ 2 - y 1 ^ 2) - μ + μ) ^ 2 + (4 * y 0 * y 1) ^ 2) =
        2 * zNormSq y := by
      rw [show (2 * (y 0 ^ 2 - y 1 ^ 2) - μ + μ) ^ 2 + (4 * y 0 * y 1) ^ 2 =
        (2 * zNormSq y) ^ 2 by unfold zNormSq; ring]
      exact Real.sqrt_sq (by positivity)
    have hr2 : Real.sqrt ((2 * (y 0 ^ 2 - y 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * y 0 * y 1) ^ 2) =
        Real.sqrt (secondCollisionDistanceSq y) := by
      congr 1; unfold secondCollisionDistanceSq; ring
    have hSpos : 0 < Real.sqrt (secondCollisionDistanceSq y) := Real.sqrt_pos.2 hDy
    simp only [jacobiHamiltonian, leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hr1, hr2]
    unfold leviCivitaHamiltonian wNormSq
    have hy' : zNormSq y ≠ 0 := hy.ne'
    unfold zNormSq at hy' ⊢
    field_simp
    ring
  -- the Jacobi point and its collision-freeness
  set x := leviCivitaToJacobi μ s with hx
  have hx0 : x 0 = 2 * (s 0 ^ 2 - s 1 ^ 2) - μ := by simp [hx, leviCivitaToJacobi, leviCivitaPosition]
  have hx1 : x 1 = 4 * s 0 * s 1 := by simp [hx, leviCivitaToJacobi, leviCivitaPosition]
  have hfree : collisionFree μ x := by
    constructor
    · rw [hx0, hx1]
      have : (2 * (s 0 ^ 2 - s 1 ^ 2) - μ + μ) ^ 2 + (4 * s 0 * s 1) ^ 2 = (2 * zNormSq s) ^ 2 := by
        unfold zNormSq; ring
      rw [this]; positivity
    · rw [hx0, hx1]
      have : (2 * (s 0 ^ 2 - s 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * s 0 * s 1) ^ 2 =
          secondCollisionDistanceSq s := by unfold secondCollisionDistanceSq; ring
      rw [this]; exact hD
  have hJdiff := jacobi_collisionFree_differentiableAt μ x hfree
  -- every directional derivative of the Jacobi Hamiltonian vanishes at `x`
  have key : ∀ e : Phase, fderiv ℝ (jacobiHamiltonian μ) x e = 0 := by
    intro e
    set P := s 0 ^ 2 + s 1 ^ 2 with hP
    have hPpos : 0 < P := hz
    set al := (e 0 * s 0 + e 1 * s 1) / (4 * P)
    set be := (e 1 * s 0 - e 0 * s 1) / (4 * P)
    set ga := (s 0 ^ 2 * e 0 * s 2 + s 0 ^ 2 * e 1 * s 3 - 2 * s 0 * s 1 * e 0 * s 3
      + 2 * s 0 * s 1 * e 1 * s 2 - s 1 ^ 2 * e 0 * s 2 - s 1 ^ 2 * e 1 * s 3
      + 4 * P ^ 2 * (s 0 * e 2 + s 1 * e 3)) / (4 * P ^ 2)
    set et := (s 0 ^ 2 * e 0 * s 3 - s 0 ^ 2 * e 1 * s 2 + 2 * s 0 * s 1 * e 0 * s 2
      + 2 * s 0 * s 1 * e 1 * s 3 - s 1 ^ 2 * e 0 * s 3 + s 1 ^ 2 * e 1 * s 2
      + 4 * P ^ 2 * (s 0 * e 3 - s 1 * e 2)) / (4 * P ^ 2)
    set δ : Phase := ![al, be, ga, et] with hδ
    set σ : ℝ → Phase := fun t => s + t • δ with hσ
    have hσ0 : σ 0 = s := by simp [hσ]
    have hl : ∀ i : Fin 4, HasDerivAt (fun t : ℝ => s i + t * δ i) (δ i) 0 := fun i => by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δ i)).const_add (s i)
    have hPne : P ≠ 0 := hPpos.ne'
    -- the Jacobi image of the line moves with velocity `e`
    have hΦ : HasDerivAt (fun t => leviCivitaToJacobi μ (σ t)) e 0 := by
      rw [hasDerivAt_pi]
      intro j
      fin_cases j
      · have hf : (fun t => leviCivitaToJacobi μ (σ t) 0) =
            fun t => 2 * ((s 0 + t * δ 0) ^ 2 - (s 1 + t * δ 1) ^ 2) - μ := by
          funext t; simp [leviCivitaToJacobi, leviCivitaPosition, hσ]
        simp only [Fin.zero_eta, Fin.isValue]
        rw [hf]
        refine ((((hl 0).fun_pow 2).fun_sub ((hl 1).fun_pow 2)).const_mul 2 |>.sub_const μ).congr_deriv ?_
        simp [hδ, al, be]; field_simp; ring
      · have hf : (fun t => leviCivitaToJacobi μ (σ t) 1) =
            fun t => 4 * (s 0 + t * δ 0) * (s 1 + t * δ 1) := by
          funext t; simp [leviCivitaToJacobi, leviCivitaPosition, hσ]
        simp only [Fin.mk_one, Fin.isValue]
        rw [hf]
        refine (((hl 0).const_mul 4).fun_mul (hl 1)).congr_deriv ?_
        simp [hδ, al, be]; field_simp; ring
      · have hf : (fun t => leviCivitaToJacobi μ (σ t) 2) =
            fun t => ((s 2 + t * δ 2) * (s 0 + t * δ 0) - (s 3 + t * δ 3) * (s 1 + t * δ 1)) /
              ((s 0 + t * δ 0) ^ 2 + (s 1 + t * δ 1) ^ 2) := by
          funext t; simp [leviCivitaToJacobi, leviCivitaMomentum, zNormSq, hσ]
        simp only [Fin.reduceFinMk, Fin.isValue]
        rw [hf]
        refine ((((hl 2).fun_mul (hl 0)).fun_sub ((hl 3).fun_mul (hl 1))).fun_div
          (((hl 0).fun_pow 2).fun_add ((hl 1).fun_pow 2)) (by simpa using hPne)).congr_deriv ?_
        have hPne' : s 0 ^ 2 + s 1 ^ 2 ≠ 0 := hPne
        simp [hδ, al, be, ga, et, hP]; field_simp; ring
      · have hf : (fun t => leviCivitaToJacobi μ (σ t) 3) =
            fun t => ((s 2 + t * δ 2) * (s 1 + t * δ 1) + (s 3 + t * δ 3) * (s 0 + t * δ 0)) /
              ((s 0 + t * δ 0) ^ 2 + (s 1 + t * δ 1) ^ 2) := by
          funext t; simp [leviCivitaToJacobi, leviCivitaMomentum, zNormSq, hσ]
        simp only [Fin.reduceFinMk, Fin.isValue]
        rw [hf]
        refine ((((hl 2).fun_mul (hl 1)).fun_add ((hl 3).fun_mul (hl 0))).fun_div
          (((hl 0).fun_pow 2).fun_add ((hl 1).fun_pow 2)) (by simpa using hPne)).congr_deriv ?_
        have hPne' : s 0 ^ 2 + s 1 ^ 2 ≠ 0 := hPne
        simp [hδ, al, be, ga, et, hP]; field_simp; ring
    -- the chain rule on the Jacobi side
    have hσ0 : σ 0 = s := by simp [hσ]
    have hF : HasFDerivAt (jacobiHamiltonian μ) (fderiv ℝ (jacobiHamiltonian μ) x)
        ((fun t => leviCivitaToJacobi μ (σ t)) 0) := by
      simpa [hσ0, hx] using hJdiff.hasFDerivAt
    have hcomp := hF.comp_hasDerivAt (0 : ℝ) hΦ
    -- the Levi-Civita side
    have hσd : HasDerivAt σ δ 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add s
      simpa [hσ] using this
    have hKF : HasFDerivAt (leviCivitaHamiltonian μ c) (fderiv ℝ (leviCivitaHamiltonian μ c) s)
        (σ 0) := by rw [hσ0]; exact hKdiff.hasFDerivAt
    have hKσ := hKF.comp_hasDerivAt (0 : ℝ) hσd
    rw [hdK] at hKσ
    have hzdiff : Differentiable ℝ zNormSq := by unfold zNormSq; fun_prop
    have hPσ := ((hzdiff (σ 0)).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hσd
    have hquot := (hKσ.div hPσ (by simpa [hσ0] using hz.ne')).sub_const c
    have hKs : leviCivitaHamiltonian μ c (σ 0) = 0 := by rw [hσ0]; exact hK
    -- the two sides agree near `t = 0`
    have hcontσ : Continuous σ := by
      simp only [hσ]; fun_prop
    have ev1 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < zNormSq (σ t) := by
      have := (hzdiff.continuous.comp hcontσ).continuousAt (x := 0)
      exact this.eventually (lt_mem_nhds (by simpa [Function.comp, hσ0] using hz))
    have hDc : Continuous secondCollisionDistanceSq := by
      unfold secondCollisionDistanceSq; fun_prop
    have ev2 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < secondCollisionDistanceSq (σ t) := by
      have := (hDc.comp hcontσ).continuousAt (x := 0)
      exact this.eventually (lt_mem_nhds (by simpa [Function.comp, hσ0] using hD))
    have heq : (fun t => jacobiHamiltonian μ (leviCivitaToJacobi μ (σ t))) =ᶠ[𝓝 (0 : ℝ)]
        (fun t => leviCivitaHamiltonian μ c (σ t) / zNormSq (σ t) - c) := by
      filter_upwards [ev1, ev2] with t h1 h2
      exact hident (σ t) h1 h2
    have h2 := hquot.congr_of_eventuallyEq heq
    have huniq := hcomp.unique h2
    rw [huniq]
    simp only [Function.comp, hKs, ContinuousLinearMap.zero_apply]
    simp
  have hzero : fderiv ℝ (jacobiHamiltonian μ) x = 0 := ContinuousLinearMap.ext key
  have hcrit : isCriticalPoint (jacobiHamiltonian μ) x := ⟨hJdiff, hzero⟩
  have hval : jacobiHamiltonian μ x = -c := by
    rw [hx, hident s hz hD, hK]; simp
  have hmem : -c ∈ criticalValueSet μ := ⟨x, hfree, hcrit, hval⟩
  obtain ⟨L, hL⟩ := inner_lagrange_point_exists μ hμ0 hμ1
  have hbdd : BddBelow (criticalValueSet μ) :=
    ⟨jacobiHamiltonian μ L, inner_lagrange_minimizes_critical_energy μ hμ0 hμ1 L hL⟩
  have hle : firstCriticalValue μ ≤ -c := csInf_le hbdd hmem
  unfold belowFirstCriticalValue at hc
  linarith
