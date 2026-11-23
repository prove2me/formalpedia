-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.hsymm_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:37.382106+00:00
-- url     : https://prove2.me/submissions/dca9686f-0e67-449d-98b3-eb60b36d3546

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
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (k : ℕ) : (MvPolynomial.hsymm (Fin n) R k).IsHomogeneous k := by
  rw [hsymm_eq_sum_monomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro l hl
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum]
  exact (Finset.mem_finsuppAntidiag.mp hl).1
end Formalism.FT.SymmetricSeries
