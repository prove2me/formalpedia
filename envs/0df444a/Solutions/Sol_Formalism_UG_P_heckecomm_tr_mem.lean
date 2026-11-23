-- Prove2me | solution 1 for Formalism.UG.P.heckecomm_tr_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:29.324602+00:00
-- url     : https://prove2.me/submissions/f7768d64-5d88-4ed4-bec6-6cd587083e99

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
import Theorems.Thm_Formalism_UG_P_heckecomm_tr_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {R : Type} [CommRing R] {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution {L : Type} [Field L] (O : Subring L) (x : GL (Fin n) L)
    (hx : x ∈ GLint (Fin n) O) : heckecomm_tr x ∈ GLint (Fin n) O := by
  obtain ⟨h, rfl⟩ := hx
  refine ⟨heckecomm_tr h, ?_⟩
  apply Units.ext
  ext i j
  simp [bc, heckecomm_tr_val]
end Formalism.UG.P
