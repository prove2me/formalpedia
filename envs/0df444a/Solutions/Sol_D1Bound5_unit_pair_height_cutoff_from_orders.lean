-- Prove2me | solution 1 for D1Bound5.unit_pair_height_cutoff_from_orders
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:45:59.377274+00:00
-- url     : https://prove2.me/submissions/8687df37-c123-4617-b91e-3ea959ca24cb

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_ge_four
import Theorems.Thm_D1Bound5_ordinaryLog10_mul
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_strictMono
import Theorems.Thm_D1Bound5_ordinaryLog10_ten
import Theorems.Thm_D1Bound5_unit_pair_height_upper_from_orders

section
namespace D1Bound5





/-- Exact scalar contradiction used in the unit-pair branch. The
reciprocal is decreasing on x>=4, so no calculus is necessary. -/
theorem unit_pair_height_cutoff_scalar (s d : ℝ) (hs : 4 ≤ s)
    (hlower : 27*s-4 < d)
    (hupper : d < 7*s+617/25+(118401/2500)/(s-203/100)) : False := by
  have hden : 0 < s-(203/100 : ℝ) := by linarith only [hs]
  have hinv : (118401/2500 : ℝ)/(s-203/100) ≤ 118401/4925 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hs]
  linarith only [hs,hlower,hupper,hinv]

end D1Bound5
end

section
namespace D1Bound5







/-- The unit-pair cubic iteration and the actual all-order inequalities
force the first extension below 10^4. The conditional input merely
restricts the analytic estimates to the large regime where they apply. -/
theorem _root_.solution (S D Z : ℝ)
    (hS : 0 < S) (hD : 0 < D) (hZ : 1 ≤ Z) (hprod : S*D < 2*Z^2)
    (hgrowth : S^27/8192 < D)
    (horders : 10000 ≤ S → ∀ k : ℕ, 1 ≤ k →
      1 < 3*S*(42*S)^k/Z+Z/(2*(27*(S-1)^2/64)^k)) : S < 10000 := by
  by_contra hbad
  have hSbig : 10000 ≤ S := le_of_not_gt hbad
  have hlogS : 4 ≤ ordinaryLog10 S := ordinaryLog10_ge_four hSbig
  have hupper := unit_pair_height_upper_from_orders S D Z hSbig hD hZ hprod
    (horders hSbig)
  have hpow : S^27 < (10 : ℝ)^4*D := by
    norm_num
    nlinarith only [hgrowth,hD]
  have hlower := ordinaryLog10_strictMono (pow_pos hS 27) hpow
  rw [ordinaryLog10_pow,ordinaryLog10_mul (10^4) D (by norm_num) hD.ne',
    ordinaryLog10_pow,ordinaryLog10_ten] at hlower
  norm_num at hlower
  exact unit_pair_height_cutoff_scalar (ordinaryLog10 S) (ordinaryLog10 D) hlogS
    (by linarith only [hlower]) hupper

end D1Bound5
end
