-- Prove2me | solution 1 for Formalism.UG.P.satake_glint_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:08.293796+00:00
-- url     : https://prove2.me/submissions/fd9a767a-f77f-43e8-916e-12249a646448

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
variable {O}
variable (O)
namespace Formalism.UG.P
theorem _root_.solution {g : GL (Fin n) L} (hg : g ∈ GLint (Fin n) O) (a b : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) a b ∈ O := by
  unfold Formalism.UG.GLint at hg
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hg
  exact ((x : Matrix (Fin n) (Fin n) O) a b).2
end Formalism.UG.P
