-- Prove2me | solution 1 for Formalism.FX.rpow_eq_prod_primeFactors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:06.145715+00:00
-- url     : https://prove2.me/submissions/431bdf7d-48dc-46dd-af6c-6f8df85325e4

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_DivisorBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FX
open Finset
namespace Formalism.FX
theorem _root_.solution (e : ℝ) {n : ℕ} (hn0 : n ≠ 0) :
    (n : ℝ) ^ e = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
  rw [Finsupp.prod, Nat.support_factorization]
  push_cast
  rw [← Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hx : (0 : ℝ) ≤ p := p.cast_nonneg
  rw [← Real.rpow_natCast (p : ℝ) (n.factorization p), ← Real.rpow_mul hx,
    mul_comm ((n.factorization p : ℕ) : ℝ) e, Real.rpow_mul hx, Real.rpow_natCast]
end Formalism.FX
