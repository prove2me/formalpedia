-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.coeff_prod_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:29.390639+00:00
-- url     : https://prove2.me/submissions/d1b5b167-0a40-4ace-9d9e-551d5ff319a7

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries

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
theorem _root_.solution (i : ℕ) :
    coeff i (∏ j : σ, (1 - C (MvPolynomial.X j : MvPolynomial σ R) * X)) =
      (-1) ^ i * MvPolynomial.esymm σ R i := by
  have h1 : ∏ j : σ, (1 - C (MvPolynomial.X j : MvPolynomial σ R) * X) =
      ∑ t ∈ (univ : Finset σ).powerset,
        C ((-1) ^ t.card * ∏ j ∈ t, (MvPolynomial.X j : MvPolynomial σ R)) * X ^ t.card := by
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, map_mul, map_pow,
      map_neg, map_one]
    ring
  rw [h1, map_sum]
  simp_rw [PowerSeries.coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  have hf : ((univ : Finset σ).powerset.filter fun t => i = t.card) = (univ : Finset σ).powersetCard i := by
    rw [Finset.powersetCard_eq_filter]
    ext t
    simp [eq_comm]
  rw [hf, MvPolynomial.esymm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_powersetCard.mp ht).2]
end Formalism.FT.SymmetricSeries
