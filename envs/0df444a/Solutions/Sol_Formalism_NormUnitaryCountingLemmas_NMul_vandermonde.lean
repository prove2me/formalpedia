-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.vandermonde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:21.42558+00:00
-- url     : https://prove2.me/submissions/1fcd1559-ce5c-4898-9a02-ced655123488

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.NMul
namespace Formalism.NormUnitaryCountingLemmas.NMul
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (m : ℕ) :
    ∑ l ∈ finsuppAntidiag (univ : Finset ι) m, ∏ k, (c k).choose (l k) =
      (∑ k, c k).choose m := by
  have h1 : (∑ k, c k).choose m = PowerSeries.coeff m
      (((∏ k, (1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ)) : PowerSeries ℕ) := by
    rw [Polynomial.coeff_coe, Finset.prod_pow_eq_pow_sum, Polynomial.coeff_one_add_X_pow,
      Nat.cast_id]
  have h2 : (((∏ k, (1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ)) : PowerSeries ℕ)
      = ∏ k, (((1 + Polynomial.X : Polynomial ℕ) ^ (c k) : Polynomial ℕ) : PowerSeries ℕ) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℕ)) _ _
  rw [h1, h2, PowerSeries.coeff_prod]
  refine sum_congr rfl fun l _ => prod_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Nat.cast_id]
end Formalism.NormUnitaryCountingLemmas.NMul
