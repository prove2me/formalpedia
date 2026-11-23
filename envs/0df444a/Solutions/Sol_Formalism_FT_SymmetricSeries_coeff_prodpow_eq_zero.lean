-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.coeff_prodpow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:34.771945+00:00
-- url     : https://prove2.me/submissions/56623047-3a53-410f-acaf-8188a8dfe8b2

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_prodpow_eq
import Theorems.Thm_Formalism_FT_SymmetricSeries_prodpow_hom

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
theorem _root_.solution (α d : Fin n →₀ ℕ) (h : wt α ≠ d.degree) :
    MvPowerSeries.coeff d (α.prod (fun j e => hv R n j ^ e)) = 0 := by
  rw [prodpow_eq, MvPolynomial.coeff_coe]
  exact (prodpow_hom α).coeff_eq_zero (Ne.symm h)
end Formalism.FT.SymmetricSeries
