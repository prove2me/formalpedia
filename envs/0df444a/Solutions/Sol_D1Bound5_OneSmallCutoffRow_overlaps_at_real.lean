-- Prove2me | solution 1 for D1Bound5.OneSmallCutoffRow.overlaps_at_real
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:40.897058+00:00
-- url     : https://prove2.me/submissions/85c9a7d4-0624-4b0e-8b77-cf14c1d28b91

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5

/-- Every strict rational overlap at the cutoff remains strict for all
larger real squared fourth moduli. -/
theorem _root_.solution (r : OneSmallCutoffRow)
    (hv : r.Valid) (x : ℝ) (hx : (r.triple.cutoff : ℝ) ≤ x)
    (e : ℚ × ℕ) (he : e ∈ r.overlaps) :
    1 < (e.1 : ℝ)*x^e.2 := by
  obtain ⟨hcut,hAN,hB,hBS,hq,hqle,hq1,hD,hphi,hp6,hp5,hsep,hK,
    hM2,hMn,hM3,hM4,hM5,hMbs,hover,htail⟩ := hv
  have hn : (0 : ℝ) < r.triple.cutoff := by
    have hn' : (1024 : ℝ) ≤ r.triple.cutoff := by exact_mod_cast hcut
    linarith only [hn']
  have hseed : 1 < (e.1 : ℝ)*(r.triple.cutoff : ℝ)^e.2 := by
    exact_mod_cast hover e he
  have hc : 0 < (e.1 : ℝ) := by
    by_contra hh
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg
      (le_of_not_gt hh) (pow_nonneg hn.le e.2)
    linarith only [hseed,hnonpos]
  have hp : (r.triple.cutoff : ℝ)^e.2 ≤ x^e.2 := by gcongr
  exact hseed.trans_le (mul_le_mul_of_nonneg_left hp hc.le)





end D1Bound5
end
