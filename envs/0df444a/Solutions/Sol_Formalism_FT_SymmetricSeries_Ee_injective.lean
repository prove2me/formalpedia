-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.Ee_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:58.833818+00:00
-- url     : https://prove2.me/submissions/0b2f8607-4cc8-408a-a6bf-b8f6dc5dacea

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
variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}
variable (R n)
variable {R n}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution : Function.Injective (Ee R n) := by
  intro p q h
  apply MvPolynomial.esymmAlgHom_fin_injective R (le_refl n)
  apply Subtype.ext
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.esymmAlgHom_apply]
  exact h
end Formalism.FT.SymmetricSeries
