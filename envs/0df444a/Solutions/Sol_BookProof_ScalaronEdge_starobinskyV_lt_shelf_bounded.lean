-- Prove2me | solution 1 for BookProof.ScalaronEdge.starobinskyV_lt_shelf_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:43:03.763087+00:00
-- url     : https://prove2.me/submissions/5ca1a434-3697-4eac-9d17-8028762e3f9d

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.starobinskyV_lt_shelf_bounded
import Mathlib
import Definitions.Def_ChapterScalaronEdge
open BookProof.ScalaronEdge










open Complex Real MeasureTheory Function SchwartzMap ComplexOrder
open BookProof.Starobinsky
open BookProof.ScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.FarisLavine
open BookProof.WallEsaSemibounded
open BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert



variable (M alpha : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (hM : 0 < M) (halpha : 0 < alpha) (c : ℝ) (hc : 0 < c)
    (hcs : c < edgeShelf M alpha) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ x : ℝ, scalV M alpha x < c → x ∈ Set.Icc (-A) B := by

  set K : ℝ := M ^ 4 / (16 * alpha) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hcK : c < K := by
    have h1 : M ^ 4 / (32 * alpha) < M ^ 4 / (16 * alpha) :=
      div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
    rw [hK]
    unfold edgeShelf at hcs
    linarith
  set a : ℝ := Real.sqrt (2 / 3) / M with ha
  have hapos : 0 < a := div_pos (Real.sqrt_pos.mpr (by norm_num)) hM
  set s : ℝ := Real.sqrt (c / K) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs1 : s < 1 := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by positivity) ((div_lt_one hKpos).mpr hcK)
  have hssq : s ^ 2 = c / K := Real.sq_sqrt (by positivity)
  refine ⟨Real.log (1 + s) / a, -Real.log (1 - s) / a, div_pos (Real.log_pos (by linarith))
    hapos, div_pos (by simpa using Real.log_neg (by linarith) (by linarith)) hapos, ?_⟩
  intro x hx
  have hexp : -(Real.sqrt (2 / 3)) * x / M = -(a * x) := by rw [ha]; field_simp
  rw [scalV, starobinskyV, hexp] at hx
  set E : ℝ := Real.exp (-(a * x)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hsq : (1 - E) ^ 2 < s ^ 2 := by
    rw [hssq, ← hK] at *
    rw [lt_div_iff₀ hKpos]
    nlinarith
  have h1 : -s < 1 - E := by nlinarith
  have h2 : 1 - E < s := by nlinarith
  constructor
  · have hE1 : Real.exp (-(a * x)) < Real.exp (Real.log (1 + s)) := by
      rw [Real.exp_log (by linarith), ← hE]; linarith
    have h3 : -(a * x) < Real.log (1 + s) := Real.exp_lt_exp.mp hE1
    rw [neg_le, le_div_iff₀ hapos]
    nlinarith
  · have hE2 : Real.exp (Real.log (1 - s)) < Real.exp (-(a * x)) := by
      rw [Real.exp_log (by linarith), ← hE]; linarith
    have h3 : Real.log (1 - s) < -(a * x) := Real.exp_lt_exp.mp hE2
    rw [le_div_iff₀ hapos]
    nlinarith
