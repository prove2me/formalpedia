-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.esymm_hsymm_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:07.130172+00:00
-- url     : https://prove2.me/submissions/de5e183e-8822-454b-aab4-e97e6eb47707

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_geom_mul
import Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_prod_one_sub
import Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_prod_geom

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
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ range (k + 1), (-1) ^ i * MvPolynomial.esymm σ R i * MvPolynomial.hsymm σ R (k - i) = 0 := by
  have hAB : (∏ j : σ, (1 - PowerSeries.C (MvPolynomial.X j : MvPolynomial σ R) * PowerSeries.X)) *
      (∏ j : σ, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial σ R) ^ m)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => geom_mul _
  have h := congrArg (PowerSeries.coeff k) hAB
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, PowerSeries.coeff_one,
    if_neg (by omega)] at h
  simp only [coeff_prod_one_sub, coeff_prod_geom] at h
  exact h
end Formalism.FT.SymmetricSeries
