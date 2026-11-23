-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.coeff_Eh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:34.734096+00:00
-- url     : https://prove2.me/submissions/c836c7aa-bed1-47f6-bd31-4ef55f876ea1

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_hasSubst_hv
import Theorems.Thm_Formalism_FT_SymmetricSeries_coe_Eh

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
theorem _root_.solution (P : MvPolynomial (Fin n) R) (d : Fin n →₀ ℕ) :
    MvPolynomial.coeff d (Eh R n P) =
      ∑ᶠ α, MvPolynomial.coeff α P • MvPowerSeries.coeff d (α.prod fun j e => hv R n j ^ e) := by
  rw [← MvPolynomial.coeff_coe, coe_Eh, MvPowerSeries.coeff_subst hasSubst_hv]
  simp only [MvPolynomial.coeff_coe]
end Formalism.FT.SymmetricSeries
