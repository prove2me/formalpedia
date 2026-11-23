-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.prodpow_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:09.053752+00:00
-- url     : https://prove2.me/submissions/8f8c23b9-a1f0-4aff-abe1-d87be3760ad4

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_hsymm_isHomogeneous

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
theorem _root_.solution (α : Fin n →₀ ℕ) :
    (∏ j : Fin n, (MvPolynomial.hsymm (Fin n) R (j + 1)) ^ (α j)).IsHomogeneous (wt α) := by
  unfold wt
  apply MvPolynomial.IsHomogeneous.prod
  intro j _
  exact (hsymm_isHomogeneous _).pow _
end Formalism.FT.SymmetricSeries
