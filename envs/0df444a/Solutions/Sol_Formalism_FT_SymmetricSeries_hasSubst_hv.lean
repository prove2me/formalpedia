-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.hasSubst_hv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:07.165002+00:00
-- url     : https://prove2.me/submissions/da7f1b2e-c42f-461e-8964-84bd172d0059

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
theorem _root_.solution : MvPowerSeries.HasSubst (hv R n) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro j
  simp only [hv, Formalism.FT.hPS]
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
  exact (hsymm_isHomogeneous _).coeff_eq_zero (by simp)
end Formalism.FT.SymmetricSeries
