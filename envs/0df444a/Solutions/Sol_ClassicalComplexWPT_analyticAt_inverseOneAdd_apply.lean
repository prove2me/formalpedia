-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_inverseOneAdd_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:02:01.76883+00:00
-- url     : https://prove2.me/submissions/ce79a2dd-290d-4671-bcf2-467a47a9530b

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero



set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
namespace ClassicalComplexWPT
theorem _root_.solution
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : X →L[ℂ] (E →L[ℂ] E)) (b : X →L[ℂ] E) (x : X) (hK : ‖K x‖ < 1) :
    AnalyticAt ℂ (fun y ↦ Ring.inverse (1 + K y) (b y)) x := by
  let op : X → (E →L[ℂ] E) := fun y ↦ 1 + K y
  have hop : AnalyticAt ℂ op x := analyticAt_const.add (K.analyticAt x)
  let hneg : ‖-(K x)‖ < 1 := by simpa using hK
  let z := Units.oneSub (-(K x)) hneg
  have hz : (z : E →L[ℂ] E) = op x := by simp [z, op, sub_eq_add_neg]
  have hinvAt : AnalyticAt ℂ Ring.inverse (op x) := by
    rw [← hz]
    exact analyticAt_inverse z
  have hinv : AnalyticAt ℂ (fun y ↦ Ring.inverse (op y)) x := by
    simpa [Function.comp_def] using hinvAt.comp hop
  have happ := (ContinuousLinearMap.apply ℂ E).analyticAt_bilinear
    (b x, Ring.inverse (op x))
  have hpair := (b.analyticAt x).prod hinv
  have hcomp := AnalyticAt.comp (x := x) happ hpair
  simpa [op, Function.comp_def] using hcomp
end ClassicalComplexWPT
