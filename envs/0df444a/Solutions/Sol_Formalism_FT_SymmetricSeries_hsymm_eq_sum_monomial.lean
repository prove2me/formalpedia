-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.hsymm_eq_sum_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:11.98409+00:00
-- url     : https://prove2.me/submissions/ab7809dd-1e64-44ab-9275-353c554ac3a7

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_prod_map_X_eq_monomial
import Theorems.Thm_Formalism_FT_SymmetricSeries_toFinsupp_sum

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
theorem _root_.solution (k : ℕ) :
    MvPolynomial.hsymm σ R k =
      ∑ l ∈ finsuppAntidiag (univ : Finset σ) k, MvPolynomial.monomial l 1 := by
  rw [MvPolynomial.hsymm]
  simp_rw [prod_map_X_eq_monomial]
  refine Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1)
    (fun l hl => ⟨Finsupp.toMultiset l, by
      rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact (Finset.mem_finsuppAntidiag.mp hl).1⟩) ?_ ?_ ?_ ?_ ?_
  · intro s _
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by rw [toFinsupp_sum]; exact s.2, Finset.subset_univ _⟩
  · intro l _
    exact Finset.mem_univ _
  · intro s _
    apply Subtype.ext
    simp
  · intro l _
    simp
  · intro s _
    rfl
end Formalism.FT.SymmetricSeries
