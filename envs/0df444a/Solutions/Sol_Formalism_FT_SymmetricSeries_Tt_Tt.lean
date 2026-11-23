-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.Tt_Tt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:33.644827+00:00
-- url     : https://prove2.me/submissions/e7426cb1-bc22-4c44-aa39-491626099849

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_Ee_injective
import Theorems.Thm_Formalism_FT_SymmetricSeries_Ee_comp_Tt
import Theorems.Thm_Formalism_FT_SymmetricSeries_Eh_comp_Tt

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
variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}
variable (R n)
variable {R n}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (q : MvPolynomial (Fin n) R) : Tt R n (Tt R n q) = q := by
  apply Ee_injective
  have h1 : (Ee R n).comp ((Tt R n).comp (Tt R n)) = Ee R n := by
    rw [← AlgHom.comp_assoc, Ee_comp_Tt, Eh_comp_Tt]
  exact congrArg (fun φ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R => φ q) h1
end Formalism.FT.SymmetricSeries
