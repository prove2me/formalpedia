-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.far_region_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:45.817598+00:00
-- url     : https://prove2.me/submissions/4f6472cd-f3b8-4cdc-81e2-27e35b98e803

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
theorem _root_.solution : FarCount := by
  intro ι _ _ n r τ k hτ hτ1 hk hr
  have hf0 : (Fintype.card ι) ≠ 0 := Fintype.card_ne_zero
  have hfpos : (0:ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hf0
  have hk0 : 0 < k := by linarith
  have eP : (∏ v, k * Real.exp (r v)) ^ ((1 : ℝ) / Fintype.card ι)
      = k * Real.exp ((∑ v, r v) / Fintype.card ι) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ,
      Real.mul_rpow (by positivity) (by positivity), one_div,
      Real.pow_rpow_inv_natCast hk0.le hf0, ← Real.exp_mul, div_eq_mul_inv]
  rw [eP]
  have hR : 0 ≤ (∑ v, r v) / Fintype.card ι := div_nonneg (Finset.sum_nonneg fun v _ => hr v) hfpos.le
  set E := Real.exp ((∑ v, r v) / Fintype.card ι) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hR
  have hτ2 : τ ^ 2 ≤ 1 := pow_le_one₀ hτ.le hτ1
  have hτ20 : 0 < τ ^ 2 := by positivity
  have h1 : 1 ≤ k * E / τ ^ 2 := by
    rw [le_div_iff₀ hτ20]; nlinarith
  have h2 : 1 + 2 * (k * E) / τ ^ 2 ≤ 3 * k / τ ^ 2 * E := by
    have e : 3 * k / τ ^ 2 * E = 3 * (k * E / τ ^ 2) := by ring
    have e' : 2 * (k * E) / τ ^ 2 = 2 * (k * E / τ ^ 2) := by ring
    rw [e, e']; linarith
  calc (1 + 2 * (k * E) / τ ^ 2) ^ (2 * n ^ 2 * Fintype.card ι)
      ≤ (3 * k / τ ^ 2 * E) ^ (2 * n ^ 2 * Fintype.card ι) := by
        apply pow_le_pow_left₀ (by positivity) h2
    _ = (3 * k / τ ^ 2) ^ (2 * n ^ 2 * Fintype.card ι) * E ^ (2 * n ^ 2 * Fintype.card ι) := mul_pow _ _ _
    _ = _ := by
      congr 1
      rw [hE, ← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
end Formalism.HermitianLatticeCounting.P
