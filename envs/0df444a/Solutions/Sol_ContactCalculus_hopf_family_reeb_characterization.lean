-- Prove2me | solution 1 for ContactCalculus.hopf_family_reeb_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T15:41:05.725079+00:00
-- url     : https://prove2.me/submissions/4135f91c-d1e8-4bdc-bd82-a8fa3938dff7

import Definitions.Def_GrayStability_HopfFamily
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open GrayStability
open scoped ContDiff

lemma sphere_smooth : ContDiff ℝ ∞ unitSphereEquation := by
  unfold unitSphereEquation
  fun_prop

lemma sphere_derivative (y v : E 4) (i : Fin 1) :
    fderiv ℝ unitSphereEquation y v i = 2 * (∑ j, y j * v j) := by
  have hd : HasFDerivAt unitSphereEquation
      (ContinuousLinearMap.pi (fun _ : Fin 1 =>
        ∑ j : Fin 4, (2 * y j) • coordCovector j)) y := by
    apply hasFDerivAt_pi.mpr
    intro k
    convert ((HasFDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      ((coordCovector j).hasFDerivAt).pow 2)).sub_const 1) using 1 <;>
      simp [unitSphereEquation, coordCovector]
  rw [hd.fderiv]
  simp [coordCovector, Finset.mul_sum, mul_assoc]

lemma sphere_tangent (y v : E 4) :
    v ∈ tangentSpace unitSphereEquation y ↔ ∑ j, y j * v j = 0 := by
  change fderiv ℝ unitSphereEquation y v = 0 ↔ _
  constructor
  · intro h
    have he := congrFun h 0
    rw [sphere_derivative] at he
    change 2 * (∑ j, y j * v j) = 0 at he
    linarith
  · intro h
    ext i
    simp [sphere_derivative, h]

lemma sphere_norm (y : E 4) (hy : y ∈ levelSet unitSphereEquation) :
    y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 = 1 := by
  have h := congrFun hy 0
  simp [unitSphereEquation, Fin.sum_univ_succ] at h
  linarith

lemma sphere_regular (y : E 4) (hy : y ∈ levelSet unitSphereEquation) :
    Function.Surjective (fderiv ℝ unitSphereEquation y) := by
  intro a
  refine ⟨(a 0 / 2) • y, ?_⟩
  have hn := sphere_norm y hy
  ext i
  fin_cases i
  simp [sphere_derivative, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul]
  nlinarith [congrArg (fun r : ℝ => a 0 * r) hn]

lemma hopf_derivative (t : ℝ) (y : E 4) :
    HasFDerivAt (hopfFamily t)
      (((coordCovector 0).smulRight (coordCovector 1) -
        (coordCovector 1).smulRight (coordCovector 0)) +
        (1 + t) • ((coordCovector 2).smulRight (coordCovector 3) -
        (coordCovector 3).smulRight (coordCovector 2))) y := by
  exact (((coordCovector 0).smulRight (coordCovector 1) -
    (coordCovector 1).smulRight (coordCovector 0)) +
    (1 + t) • ((coordCovector 2).smulRight (coordCovector 3) -
    (coordCovector 3).smulRight (coordCovector 2))).hasFDerivAt

lemma hopf_smooth (t : ℝ) : ContDiff ℝ ∞ (hopfFamily t) := by
  unfold hopfFamily coordCovector
  fun_prop

lemma hopf_value (t : ℝ) (y v : E 4) :
    hopfFamily t y v = y 0 * v 1 - y 1 * v 0 +
      (1 + t) * (y 2 * v 3 - y 3 * v 2) := by
  simp [hopfFamily, coordCovector]

lemma hopf_exterior (t : ℝ) (y u v : E 4) :
    extDerivOneForm (hopfFamily t) y u v =
      2 * (u 0 * v 1 - u 1 * v 0 + (1 + t) * (u 2 * v 3 - u 3 * v 2)) := by
  unfold extDerivOneForm
  rw [(hopf_derivative t y).fderiv]
  simp [coordCovector]
  ring

theorem solution (t : ℝ) (ht : 0 ≤ t)
    (y : E 4) (hy : y ∈ levelSet unitSphereEquation) (u : E 4) :
    (u ∈ tangentSpace unitSphereEquation y ∧ hopfFamily t y u = 1 ∧
      ∀ v ∈ tangentSpace unitSphereEquation y,
        extDerivOneForm (hopfFamily t) y u v = 0) ↔
      u = ![-y 1, y 0, -y 3 / (1 + t), y 2 / (1 + t)] := by
  have ha : 1 + t ≠ 0 := by linarith
  have hn := sphere_norm y hy
  constructor
  · rintro ⟨_, hval, hker⟩
    rw [hopf_value] at hval
    have hp (i : Fin 4) :
        (Pi.single i 1 - y i • y : E 4) ∈ tangentSpace unitSphereEquation y := by
      have hn' := congrArg (fun a : ℝ => y i * a) hn
      rw [sphere_tangent]
      fin_cases i <;>
        simp [Fin.sum_univ_succ, Pi.single_apply, Pi.smul_apply, smul_eq_mul] at hn' ⊢
        <;> nlinarith only [hn']
    have h0 := hker _ (hp 0)
    have h1 := hker _ (hp 1)
    have h2 := hker _ (hp 2)
    have h3 := hker _ (hp 3)
    simp [hopf_exterior, Pi.smul_apply, smul_eq_mul] at h0 h1 h2 h3
    have hv0 := congrArg (fun a : ℝ => y 0 * a) hval
    have hv1 := congrArg (fun a : ℝ => y 1 * a) hval
    have hv2 := congrArg (fun a : ℝ => y 2 * a) hval
    have hv3 := congrArg (fun a : ℝ => y 3 * a) hval
    ext i
    fin_cases i
    · change u 0 = -y 1
      nlinarith only [h1, hv1]
    · change u 1 = y 0
      nlinarith only [h0, hv0]
    · change u 2 = -y 3 / (1 + t)
      apply (eq_div_iff ha).mpr
      nlinarith only [h3, hv3]
    · change u 3 = y 2 / (1 + t)
      apply (eq_div_iff ha).mpr
      nlinarith only [h2, hv2]
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [sphere_tangent]
      simp [Fin.sum_univ_succ]
      field_simp
      <;> ring
    · rw [hopf_value]
      simp
      field_simp
      nlinarith [hn]
    · intro v hv
      rw [sphere_tangent] at hv
      simp [Fin.sum_univ_succ] at hv
      rw [hopf_exterior]
      simp
      field_simp
      nlinarith [hv]
