-- Prove2me | solution 1 for ContactCalculus.strict_hopf_pullback_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T15:42:10.57848+00:00
-- url     : https://prove2.me/submissions/f2683594-03a7-4f32-84e1-860f19d9b521

import Theorems.Thm_ContactCalculus_hopf_family_reeb_characterization
import Theorems.Thm_ContactCalculus_strict_pullback_preserves_reeb_equations_on_regular_level
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

lemma hopf_smooth (t : ℝ) : ContDiff ℝ ∞ (hopfFamily t) := by
  unfold hopfFamily coordCovector
  fun_prop

theorem solution (t : ℝ) (ht : 0 ≤ t)
    (f : E 4 → E 4) (hf : ContDiff ℝ ∞ f)
    (hbij : Set.BijOn f (levelSet unitSphereEquation) (levelSet unitSphereEquation))
    (hinj : ∀ y ∈ levelSet unitSphereEquation,
      Set.InjOn (fderiv ℝ f y) (tangentSpace unitSphereEquation y))
    (hα : ∀ y ∈ levelSet unitSphereEquation, ∀ v ∈ tangentSpace unitSphereEquation y,
      pullback f (hopfFamily t) y v = hopfFamily 0 y v) :
    ∀ y ∈ levelSet unitSphereEquation,
      fderiv ℝ f y ![-y 1, y 0, -y 3, y 2] =
        ![-(f y) 1, (f y) 0, -(f y) 3 / (1 + t), (f y) 2 / (1 + t)] := by
  intro y hy
  let u : E 4 := ![-y 1, y 0, -y 3, y 2]
  have hu := (ContactCalculus.hopf_family_reeb_characterization 0 (by norm_num) y hy u).mpr (by simp [u])
  have htransport := ContactCalculus.strict_pullback_preserves_reeb_equations_on_regular_level
    unitSphereEquation sphere_smooth sphere_regular (hopfFamily t) (hopfFamily 0)
    (hopf_smooth t) (hopf_smooth 0) f hf hbij.1 hinj hα y hy u hu.1 hu.2.1 hu.2.2
  exact (ContactCalculus.hopf_family_reeb_characterization t ht (f y) (hbij.1 hy)
    (fderiv ℝ f y u)).mp htransport
