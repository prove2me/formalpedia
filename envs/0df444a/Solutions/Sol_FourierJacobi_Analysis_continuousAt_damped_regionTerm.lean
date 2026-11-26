-- Prove2me | solution 1 for FourierJacobi.Analysis.continuousAt_damped_regionTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:09.503518+00:00
-- url     : https://prove2.me/submissions/4391d48f-e39c-460d-8116-4f6ef2180267

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Theorems.Thm_FourierJacobi_Analysis_dampedRational_one
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.dampedRational_one

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V : ℂ) (hd : d ≠ 0)
    (h : RegionRegular t d U V) (i : Fin 50) :
    ContinuousAt (fun T : ℝ => regionTerms t d ((T : ℂ) * U) ((T : ℂ) * V) i) 1 := by
  have hp := h.p
  have hn := h.n
  have he := h.e
  have hf := h.f
  have hg := h.g
  have hct : ContinuousAt (fun T : ℝ => (T : ℂ)) 1 :=
    Complex.continuous_ofReal.continuousAt
  fin_cases i
  · change ContinuousAt (fun T : ℝ => regionTerm0 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm0
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm1 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm1
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm2 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm2
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm3 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm3
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm4 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm4
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm5 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm5
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm6 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm6
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm7 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm7
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm8 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm8
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm9 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm9
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm10 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm10
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm11 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm11
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm12 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm12
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm13 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm13
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm14 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm14
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm15 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm15
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm16 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm16
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm17 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm17
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm18 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm18
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm19 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm19
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm20 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm20
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm21 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm21
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm22 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm22
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm23 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm23
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm24 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm24
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm25 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm25
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm26 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm26
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm27 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm27
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm28 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm28
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm29 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm29
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm30 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm30
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm31 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm31
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm32 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm32
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm33 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm33
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm34 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm34
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm35 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm35
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm36 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm36
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm37 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm37
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm38 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm38
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm39 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm39
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm40 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm40
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm41 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm41
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm42 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm42
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm43 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm43
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm44 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm44
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm45 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm45
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm46 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm46
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm47 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm47
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm48 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm48
    fun_prop (disch := simp_all)
  · change ContinuousAt (fun T : ℝ => regionTerm49 t d ((T : ℂ) * U) ((T : ℂ) * V)
      (1 - d * ((T : ℂ) * V) * t) (1 - ((T : ℂ) * V) * t / d)
      (1 - ((T : ℂ) * V) ^ 2 * t ^ 2) (1 - ((T : ℂ) * U) * t ^ 2)
      (1 - ((T : ℂ) * U) * t ^ 4)) 1
    unfold regionTerm49
    fun_prop (disch := simp_all)
end FourierJacobi.Analysis
