-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_seqDivisionRemainderGlobal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:37.798175+00:00
-- url     : https://prove2.me/submissions/42649f19-709f-42ce-b2e7-65f456d63bc2

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
import Theorems.Thm_ClassicalComplexWPT_analyticAt_seqDivisionQuotientGlobal
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero


attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionOperatorInput_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionRhsInput_apply

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ)
    (pf : L1Coeff ℕ × L1Coeff ℕ) (hp : ‖pf.1‖ < 1) :
    AnalyticAt ℂ (seqDivisionRemainderGlobal d) pf := by
  have hq := analyticAt_seqDivisionQuotientGlobal d pf hp
  have happ := (convolutionRightMap (A := ℕ)).analyticAt_bilinear
    (pf.1, seqDivisionQuotientGlobal d pf)
  have hconv : AnalyticAt ℂ
      (fun x : L1Coeff ℕ × L1Coeff ℕ ↦
        convolution (seqDivisionQuotientGlobal d x) x.1) pf := by
    have hpair := (analyticAt_fst (𝕜 := ℂ)).prod hq
    simpa [Function.comp_def] using AnalyticAt.comp (x := pf) happ hpair
  have hdiff : AnalyticAt ℂ
      (fun x : L1Coeff ℕ × L1Coeff ℕ ↦
        x.2 - convolution (seqDivisionQuotientGlobal d x) x.1) pf :=
    (analyticAt_snd (𝕜 := ℂ)).sub hconv
  have hout := (seqLowCutCLM d).analyticAt
    (pf.2 - convolution (seqDivisionQuotientGlobal d pf) pf.1)
  change AnalyticAt ℂ (fun x : L1Coeff ℕ × L1Coeff ℕ ↦
    seqLowCut d (x.2 - convolution (seqDivisionQuotientGlobal d x) x.1)) pf
  have hcomp := AnalyticAt.comp (x := pf) hout hdiff
  simpa [seqLowCutCLM, Function.comp_def] using hcomp
end ClassicalComplexWPT
