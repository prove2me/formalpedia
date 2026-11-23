-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.cyclotomic_dvd_prod_X_pow_sub_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:32.514312+00:00
-- url     : https://prove2.me/submissions/680799ff-d0a1-4dfa-a7b4-54bcdb2d7e44

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prod_Ioo_eq_prod_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (hl2 : l ≠ 2) :
    Polynomial.cyclotomic l ℤ ∣
      (∏ c ∈ Finset.Ioo 0 l, ((Polynomial.X : Polynomial ℤ) ^ c - 1)) - Polynomial.C (l : ℤ) := by
  have hp : l.Prime := Fact.out
  have hl : l ≠ 0 := hp.ne_zero
  have hpos : 0 < l := hp.pos
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / l)) l :=
    Complex.isPrimitiveRoot_exp l hl
  generalize Complex.exp (2 * Real.pi * Complex.I / l) = ζ at hζ
  rw [Polynomial.cyclotomic_eq_minpoly hζ hpos]
  apply minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hpos)
  simp only [map_sub, map_prod, map_pow, Polynomial.aeval_X, map_one, Polynomial.aeval_C]
  have hs : l - 1 + 1 = l := Nat.sub_add_cancel hp.one_le
  have hζ' : IsPrimitiveRoot ζ (l - 1 + 1) := by rwa [hs]
  have h := hζ'.prod_pow_sub_one_eq_order
  rw [(hp.even_sub_one hl2).neg_one_pow, one_mul] at h
  rw [prod_Ioo_eq_prod_range, h]
  have hc : (((l - 1 : ℕ) : ℂ) + 1) = (l : ℂ) := by
    have : ((l - 1 + 1 : ℕ) : ℂ) = (l : ℂ) := by rw [hs]
    push_cast at this
    exact this
  rw [hc]
  simp
end Formalism.CohomologicalDescent.HeightDescentMinors
