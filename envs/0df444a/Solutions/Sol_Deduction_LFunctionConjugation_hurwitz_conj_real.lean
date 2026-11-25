-- Prove2me | solution 1 for Deduction.LFunctionConjugation.hurwitz_conj_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:54.332797+00:00
-- url     : https://prove2.me/submissions/cfd12400-05c7-4d2e-b96d-ca37f65f4b67

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Theorems.Thm_Deduction_LFunctionConjugation_hurwitz_conj_of_re
import Theorems.Thm_Deduction_LFunctionConjugation_differentiable_reg
import Theorems.Thm_Deduction_LFunctionConjugation_pole_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
open Deduction.LFunctionConjugation
open HurwitzZeta
namespace Deduction.LFunctionConjugation
theorem _root_.solution {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (s : ℂ) :
    hurwitzZeta a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hurwitzZeta a s) := by
  have hreg : ∀ z : ℂ, 1 < z.re → (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z)) = reg a z := by
    intro z hz
    have h1 := hurwitz_conj_of_re ha (s := (starRingEnd ℂ) z) (by rwa [Complex.conj_re])
    have h2 := pole_conj ((starRingEnd ℂ) z)
    rw [Complex.conj_conj] at h1 h2
    rw [reg, reg, map_sub, h1, h2]
  have hF : Differentiable ℂ (fun z => (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z))) :=
    fun z => differentiableAt_conj_conj_iff.mpr (differentiable_reg a _)
  have heq : (fun z => (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z))) = reg a :=
    AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (hF.differentiableOn.analyticOnNhd isOpen_univ)
      ((differentiable_reg a).differentiableOn.analyticOnNhd isOpen_univ)
      (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hreg)
  have h3 : (starRingEnd ℂ) (reg a ((starRingEnd ℂ) ((starRingEnd ℂ) s))) = reg a ((starRingEnd ℂ) s) :=
    congrFun heq _
  rw [Complex.conj_conj] at h3
  have e : ∀ w, hurwitzZeta a w = reg a w + 1 / (w - 1) / Gammaℝ w := fun w => by
    rw [reg, sub_add_cancel]
  rw [e ((starRingEnd ℂ) s), e s, map_add, ← h3, pole_conj]
end Deduction.LFunctionConjugation
