-- Prove2me | solution 1 for Formalism.UG.P.permMatrix_isUnitary_of_commute_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:23.751117+00:00
-- url     : https://prove2.me/submissions/3faf3a30-a299-479d-8a7d-a6dac0c52d37

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Theorems.Thm_P2M_Formalism_UG_P_permMatrix_mulVec__7012a139132f
import Theorems.Thm_Formalism_UG_P_fIwasawa_un_of_isometry


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (Fin.rev i) = Fin.rev (π i)) :
    fIwasawaUn σ (fIwasawaP (L := L) π) := by
  apply fIwasawa_un_of_isometry
  intro x y
  simp only [fIwasawaH, permMatrix_mulVec₂, hπ]
  exact Equiv.sum_comp π (fun k => σ (x (Fin.rev k)) * y k)
end Formalism.UG.P
