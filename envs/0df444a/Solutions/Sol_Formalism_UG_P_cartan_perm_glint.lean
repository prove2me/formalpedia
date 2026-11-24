-- Prove2me | solution 1 for Formalism.UG.P.cartan_perm_glint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:10.392972+00:00
-- url     : https://prove2.me/submissions/f7a5258c-cee2-4900-945e-9f791d6d42b0

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_Formalism_UG_P_cartan_exists_glint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
namespace Formalism.UG.P
theorem _root_.solution {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    ∃ U ∈ GLint (Fin m) O, (U : Matrix (Fin m) (Fin m) L) = τ.toPEquiv.toMatrix := by
  obtain ⟨U, hU, hUA⟩ := cartan_exists_glint O τ.toPEquiv.toMatrix τ.symm.toPEquiv.toMatrix
    (by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl])
    (by intro i j; rw [PEquiv.toMatrix_apply]; split_ifs; exacts [O.one_mem, O.zero_mem])
    (by intro i j; rw [PEquiv.toMatrix_apply]; split_ifs; exacts [O.one_mem, O.zero_mem])
  exact ⟨U, hU, hUA⟩
end Formalism.UG.P
