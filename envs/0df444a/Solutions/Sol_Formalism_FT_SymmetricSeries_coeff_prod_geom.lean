-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.coeff_prod_geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:37.993797+00:00
-- url     : https://prove2.me/submissions/0a900ce3-6e62-4a95-bc83-74ad1c4f277a

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_hsymm_eq_sum_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
open PowerSeries
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (k : ℕ) :
    coeff k (∏ j : σ, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial σ R) ^ m)) =
      MvPolynomial.hsymm σ R k := by
  rw [PowerSeries.coeff_prod, hsymm_eq_sum_monomial]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [PowerSeries.coeff_mk]
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
end Formalism.FT.SymmetricSeries
