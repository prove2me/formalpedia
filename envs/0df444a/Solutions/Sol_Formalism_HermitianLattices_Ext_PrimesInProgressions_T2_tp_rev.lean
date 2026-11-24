-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.tp_rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:55.914558+00:00
-- url     : https://prove2.me/submissions/2fa24508-ea62-4349-84c3-4f55e53ddd2c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_tp_eval
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_tp_eval_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution (n : ℕ) (z : Fin n → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) :
    ∏ i, (1 - z i * ζ) = ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by
  have h1 : ∏ i, (1 - z i * ζ) = ζ ^ n * (tp n z).eval ζ⁻¹ := by
    rw [tp_eval, ← Fin.prod_const n ζ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_sub, mul_inv_cancel₀ hζ]
    ring
  rw [h1, tp_eval_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [inv_pow, pow_sub₀ _ hζ ha']
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
