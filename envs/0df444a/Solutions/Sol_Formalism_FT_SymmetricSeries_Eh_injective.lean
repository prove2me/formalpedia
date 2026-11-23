-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.Eh_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:42.016846+00:00
-- url     : https://prove2.me/submissions/26c710bd-8773-416a-8c75-2b2a4779412b

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_Ee_injective
import Theorems.Thm_Formalism_FT_SymmetricSeries_Ee_comp_Tt
import Theorems.Thm_Formalism_FT_SymmetricSeries_Tt_Tt

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
theorem _root_.solution : Function.Injective (Eh R n) := by
  intro p q h
  have e1 : ∀ x, Ee R n (Tt R n x) = Eh R n x := fun x => by rw [← AlgHom.comp_apply, Ee_comp_Tt]
  have h1 : Ee R n (Tt R n p) = Ee R n (Tt R n q) := by rw [e1, e1, h]
  have h2 := Ee_injective h1
  rw [← Tt_Tt p, ← Tt_Tt q, h2]
end Formalism.FT.SymmetricSeries
