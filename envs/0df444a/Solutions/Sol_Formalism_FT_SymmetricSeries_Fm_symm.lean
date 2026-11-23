-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.Fm_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:20.786939+00:00
-- url     : https://prove2.me/submissions/c039f665-5a42-48d3-a1be-b158ef85ee31

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_mapDomain_of_symm
import Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_Fm

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
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (F : MvPowerSeries (Fin n) R)
    (hF : ∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F)
    (m : ℕ) : (Fm F m).IsSymmetric := by
  intro π
  ext d
  have hd : d = (d.mapDomain π.symm).mapDomain π := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hdeg : (d.mapDomain π.symm).degree = d.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, ← Equiv.sum_comp π.symm]
    simp [Finsupp.mapDomain_apply π.symm.injective]
  conv_lhs => rw [hd]
  rw [MvPolynomial.coeff_rename_mapDomain π π.injective, coeff_Fm, coeff_Fm,
    coeff_mapDomain_of_symm F hF π.symm d, hdeg]
end Formalism.FT.SymmetricSeries
