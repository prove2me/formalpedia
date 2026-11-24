-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.delta_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:07.504885+00:00
-- url     : https://prove2.me/submissions/8db7b57d-1cf2-41e9-b5e7-e9375f1f7324

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DeltaSmall := by
  intro n q f c hn hf hq hc hc9
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hqn1 : (q:ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq
    exact_mod_cast this
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hn0 : (0:ℝ) < n := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have e1 : (n:ℝ) * epsN c n f = c / ((n:ℝ)^7 * (f:ℝ)^2) := by
    unfold epsN; field_simp
  have k1 : (n:ℝ) * epsN c n f ≤ (1 / (300 * (n:ℝ)^3 * f))^2 := by
    rw [e1]
    have e2 : (1 / (300 * (n:ℝ)^3 * f))^2 = (1/90000) / ((n:ℝ)^6 * (f:ℝ)^2) := by
      field_simp; norm_num
    rw [e2]
    apply div_le_div₀ (by norm_num) hc9 (by positivity)
    have : (n:ℝ)^6 ≤ (n:ℝ)^7 := pow_le_pow_right₀ hn' (by norm_num)
    gcongr
  have k2 : Real.sqrt ((n:ℝ) * epsN c n f) ≤ 1 / (300 * (n:ℝ)^3 * f) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, k1⟩
  have hn3 : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ hn'
  have k3 : 1 / (300 * (n:ℝ)^3 * f) ≤ 1 / 300 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have he0 : 0 < epsN c n f := by unfold epsN; positivity
  have k4 : (n:ℝ) * epsN c n f ≤ 1 := by
    refine k1.trans ?_
    have : 0 ≤ 1 / (300 * (n:ℝ)^3 * f) := by positivity
    nlinarith
  refine ⟨?_, by linarith, k4, ?_⟩
  · calc 3 * Real.sqrt ((n:ℝ) * epsN c n f) * q * n * f
        ≤ 3 * (1 / (300 * (n:ℝ)^3 * f)) * n * n * f := by gcongr
      _ = 1 / (100 * n) := by field_simp; norm_num
      _ ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        linarith
  · have : (n:ℝ) * epsN c n f ≤ (1/300)^2 := by
      refine k1.trans ?_
      have : 0 ≤ 1 / (300 * (n:ℝ)^3 * f) := by positivity
      gcongr
    nlinarith
end Formalism.HermitianLatticeCounting.P
