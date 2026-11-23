-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.d_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:04.353256+00:00
-- url     : https://prove2.me/submissions/981b8838-8864-4e91-8287-3d05a3e5ba9f

import Mathlib
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral
namespace Formalism.ZF.ComplexPowerDifferenceIntegral
theorem _root_.solution {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (a : ℂ) ^ (1 - s) - ((a + 1 : ℝ) : ℂ) ^ (1 - s) - (s - 1) * ((a + 1 : ℝ) : ℂ) ^ (-s) =
      (s - 1) * eint s a := by
  unfold eint
  by_cases hs1 : s = 1
  · subst hs1; simp
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]; intro h; linarith [h.1]
  have hr : -s ≠ -1 := by intro h; apply hs1; linear_combination -h
  have hint1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume a (a + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr h0)
  rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const,
    integral_cpow (Or.inr ⟨hr, h0⟩), intervalIntegral.integral_const]
  have e : -s + 1 = 1 - s := by ring
  rw [e]
  have hs' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [Complex.real_smul]
  push_cast
  field_simp
  ring
end Formalism.ZF.ComplexPowerDifferenceIntegral
