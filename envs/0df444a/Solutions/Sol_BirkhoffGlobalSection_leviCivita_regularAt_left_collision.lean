-- Prove2me | solution 1 for BirkhoffGlobalSection.leviCivita_regularAt_left_collision
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T22:39:56.720265+00:00
-- url     : https://prove2.me/submissions/7d8d31b9-f73e-4f4b-b01d-5ba742582664

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

open BirkhoffGlobalSection

lemma lc_radial_hasDerivAt (μ c : ℝ) (s : Phase) (hD : 0 < secondCollisionDistanceSq s) :
    HasDerivAt (fun a : ℝ => leviCivitaHamiltonian μ c (fun i : Fin 4 => a * s i))
      ((s 2 ^ 2 + s 3 ^ 2) + 2 * c * (s 0 ^ 2 + s 1 ^ 2)
        + 8 * (s 0 ^ 2 + s 1 ^ 2) * (s 0 * s 3 - s 1 * s 2)
        - 2 * μ * (s 0 * s 3 + s 1 * s 2)
        - 2 * μ * (s 0 ^ 2 + s 1 ^ 2) / Real.sqrt (secondCollisionDistanceSq s)
        + μ * (s 0 ^ 2 + s 1 ^ 2) * (8 * (s 0 ^ 2 + s 1 ^ 2) ^ 2 - 4 * (s 0 ^ 2 - s 1 ^ 2)) /
          Real.sqrt (secondCollisionDistanceSq s) ^ 3) 1 := by
  have hx := hasDerivAt_id' (1 : ℝ)
  have e : ∀ i : Fin 4, HasDerivAt (fun a : ℝ => a * s i) (1 * s i) 1 := fun i => hx.mul_const (s i)
  have hin : HasDerivAt (fun a : ℝ => (2 * ((a * s 0) ^ 2 - (a * s 1) ^ 2) - 1) ^ 2 +
      (4 * (a * s 0) * (a * s 1)) ^ 2)
      (8 * (s 0 ^ 2 - s 1 ^ 2) * (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) + 64 * (s 0 * s 1) ^ 2) 1 := by
    have := ((((((e 0).fun_pow 2).fun_sub ((e 1).fun_pow 2)).const_mul 2).sub_const 1).fun_pow 2).fun_add
      ((((e 0).const_mul 4).fun_mul (e 1)).fun_pow 2)
    refine this.congr_deriv ?_
    simp; ring
  have hD' : (2 * ((1 * s 0) ^ 2 - (1 * s 1) ^ 2) - 1) ^ 2 + (4 * (1 * s 0) * (1 * s 1)) ^ 2 ≠ 0 := by
    simp only [one_mul]; exact hD.ne'
  have hS := hin.sqrt hD'
  simp only [one_mul] at hS
  unfold secondCollisionDistanceSq at hD ⊢
  have hNpos : 0 < Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) :=
    Real.sqrt_pos.2 hD
  have hsq : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) ^ 2 =
      (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2 :=
    Real.sq_sqrt hD.le
  have hW := ((((e 2).fun_pow 2).fun_add ((e 3).fun_pow 2)).div_const 2)
  have hP := (((e 0).fun_pow 2).fun_add ((e 1).fun_pow 2))
  have hL := (((e 0).fun_mul (e 3)).fun_sub ((e 1).fun_mul (e 2)))
  have hM := (((e 0).fun_mul (e 3)).fun_add ((e 1).fun_mul (e 2)))
  have htot := ((((hW.fun_add (hP.const_mul c)).sub_const ((1 - μ) / 2)).fun_add
    ((hP.const_mul 2).fun_mul hL)).fun_sub (hM.const_mul μ)).fun_sub
    ((hP.const_mul μ).fun_div hS (by simpa using hNpos.ne'))
  refine htot.congr_deriv ?_
  simp only [one_mul]
  generalize hNdef : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) = N at *
  have hNne : N ≠ 0 := hNpos.ne'
  field_simp
  linear_combination (0:ℝ) * hsq


theorem solution (μ c : ℝ)
    (hμ1 : μ < 1) (s : Phase)
    (hK : leviCivitaHamiltonian μ c s = 0)
    (hz : zNormSq s = 0) :
    fderiv ℝ (leviCivitaHamiltonian μ c) s ≠ 0 := by
  unfold zNormSq at hz
  have h0 : s 0 = 0 := by nlinarith [sq_nonneg (s 0), sq_nonneg (s 1)]
  have h1 : s 1 = 0 := by nlinarith [sq_nonneg (s 0), sq_nonneg (s 1)]
  have hD1 : secondCollisionDistanceSq s = 1 := by
    simp [secondCollisionDistanceSq, h0, h1]
  have hD : 0 < secondCollisionDistanceSq s := by rw [hD1]; norm_num
  -- the energy equation forces `|w|^2 = 1 - μ`
  have hW : s 2 ^ 2 + s 3 ^ 2 = 1 - μ := by
    unfold leviCivitaHamiltonian zNormSq wNormSq at hK
    rw [hD1, h0, h1] at hK
    simp at hK
    linarith
  -- differentiability of the Hamiltonian away from the second collision
  have hDdiff : Differentiable ℝ secondCollisionDistanceSq := by
    unfold secondCollisionDistanceSq; fun_prop
  have hSne : Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hS : DifferentiableAt ℝ (fun x : Phase => Real.sqrt (secondCollisionDistanceSq x)) s :=
    (hDdiff s).sqrt hD.ne'
  have hdiff : DifferentiableAt ℝ (leviCivitaHamiltonian μ c) s := by
    have hDne : (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2 ≠ 0 := by
      have := hD.ne'; unfold secondCollisionDistanceSq at this; exact this
    have hSne' : Real.sqrt ((2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2) ≠ 0 := by
      have := hSne; unfold secondCollisionDistanceSq at this; exact this
    unfold leviCivitaHamiltonian zNormSq wNormSq secondCollisionDistanceSq
    fun_prop (disch := assumption)
  -- compare with the radial derivative
  intro hzero
  have hrad := lc_radial_hasDerivAt μ c s hD
  have hline : HasDerivAt (fun a : ℝ => a • s) s 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const s
  have hF : HasFDerivAt (leviCivitaHamiltonian μ c) (fderiv ℝ (leviCivitaHamiltonian μ c) s)
      ((fun a : ℝ => a • s) 1) := by simpa using hdiff.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt (1 : ℝ) hline
  rw [hzero] at hcomp
  have huniq := hrad.unique hcomp
  simp [h0, h1] at huniq
  nlinarith
