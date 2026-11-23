-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.sum_valuation_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:59.423539+00:00
-- url     : https://prove2.me/submissions/6fc36bd8-7053-4899-bf13-37ae079d7ba0

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementX
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_zero
import Theorems.Thm_P2M_Formalism_DivisionValues_prod_formula__ad6919c95c2d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
namespace Formalism.PairingDivisionLocalBalance
theorem _root_.solution : SumValNat := by
  intro K _ _ _ _ n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Formalism.DivisionValues.ValuationRepresentative.vw_zero]
  · have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
    obtain ⟨h1, h2⟩ := Formalism.DivisionValues.prod_formula' K (n : K) hn0
    refine ⟨h1, ?_⟩
    rw [← h2]
    have hc : (Fintype.card (InfinitePlace K) : ℝ) * 2 = (finrank ℚ K : ℝ) := by
      have h3 := IsTotallyComplex.finrank K
      have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
      have h5 := IsTotallyComplex.nrRealPlaces_eq_zero K
      rw [h3, h4, h5]; push_cast; ring
    have hpos : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
    simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hc]
    have : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hc; linarith
    field_simp
end Formalism.PairingDivisionLocalBalance
