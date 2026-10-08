-- Prove2me | solution 1 for FriezeKannan.Continuum.l2_drop
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:15:09.911772+00:00
-- url     : https://prove2.me/submissions/81a7fdeb-d03c-4e73-9df8-ce9cb965f1aa

import Mathlib
import Definitions.Def_FriezeKannan_Continuum_Setting

open MeasureTheory

open FriezeKannan.Continuum

theorem solution (w : Sq → ℝ) (hw : MemLp w 2) (S T : Set unitInterval)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hpos : 0 < (volume S).toReal * (volume T).toReal) :
    let d := rectInt w S T / ((volume S).toReal * (volume T).toReal)
    (l2Norm (fun p => w p - cutFun S T d p) ^ 2 - l2Norm w ^ 2
        = ∫ p in S ×ˢ T, ((w p - d) ^ 2 - w p ^ 2)) ∧
    (l2Norm (fun p => w p - cutFun S T d p) ^ 2 - l2Norm w ^ 2
        = -((volume S).toReal * (volume T).toReal) * d ^ 2) ∧
    (l2Norm (fun p => w p - cutFun S T d p) ^ 2 - l2Norm w ^ 2
        = -(rectInt w S T) ^ 2 / ((volume S).toReal * (volume T).toReal)) := by
  classical
  dsimp only
  let d := rectInt w S T / ((volume S).toReal * (volume T).toReal)
  let U := S ×ˢ T
  have hU : MeasurableSet U := hS.prod hT
  have hw1 : Integrable w := hw.integrable (by norm_num)
  have hc : MemLp (cutFun S T d) 2 := (memLp_const d).indicator hU
  have hs : Integrable (fun p => (w p - cutFun S T d p)^2) := (hw.sub hc).integrable_sq
  have norm_sq (f : Sq → ℝ) : l2Norm f ^ 2 = ∫ p, f p^2 := by
    apply Real.sq_sqrt
    exact integral_nonneg (fun p => sq_nonneg _)
  have point : (fun p => (w p-cutFun S T d p)^2-w p^2) =
      U.indicator (fun p => (w p-d)^2-w p^2) := by
    funext p
    by_cases hp : p ∈ U
    · simp [cutFun, U, hp]
    · simp [cutFun, U, hp]
  have first : l2Norm (fun p => w p - cutFun S T d p)^2-l2Norm w^2 =
      ∫ p in U, ((w p-d)^2-w p^2) := by
    rw [norm_sq, norm_sq, ← integral_sub hs hw.integrable_sq, point,
      integral_indicator hU]
  have calc_int : (∫ p in U, ((w p-d)^2-w p^2)) =
      -2*d*rectInt w S T + ((volume S).toReal*(volume T).toReal)*d^2 := by
    have point2 : (fun p => (w p-d)^2-w p^2) = (fun p => -2*d*w p + d^2) := by
      funext p; ring
    rw [point2, integral_add ((hw1.restrict).const_mul _) (integrable_const _),
      integral_const_mul, integral_const]
    simp only [rectInt, U, measureReal_def, Measure.restrict_apply_univ]
    rw [show (volume : Measure Sq) = volume.prod volume from rfl,
      Measure.prod_prod, ENNReal.toReal_mul]
    ring
  have hn : (volume S).toReal*(volume T).toReal ≠ 0 := ne_of_gt hpos
  refine ⟨first, ?_, ?_⟩
  · rw [first, calc_int]
    dsimp [d]
    field_simp
    <;> ring
  · rw [first, calc_int]
    dsimp [d]
    field_simp
    <;> ring




#print axioms solution
