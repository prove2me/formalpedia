-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.traceLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:35.756383+00:00
-- url     : https://prove2.me/submissions/e90082a5-b0a1-4225-87a5-cf1fa1d3e54b

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : TraceLower := by
  intro ι _ a ha hprod
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · rw [hn, Nat.cast_zero]; exact Finset.sum_nonneg (fun v _ => ha v)
  · have hn' : (0:ℝ) < Fintype.card ι := by exact_mod_cast hn
    have amgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1:ℝ)) a
      (fun _ _ => zero_le_one) (by simpa using hn') (fun v _ => ha v)
    simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at amgm
    have h1 : 1 ≤ (∏ v, a v) ^ ((Fintype.card ι : ℝ))⁻¹ :=
      Real.one_le_rpow hprod (by positivity)
    have := h1.trans amgm
    rwa [le_div_iff₀ hn', one_mul] at this
end Formalism.HermitianLatticeCounting.P
