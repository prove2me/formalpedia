-- Prove2me | solution 1 for Formalism.UG.P.cartan_entries_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:47:57.77649+00:00
-- url     : https://prove2.me/submissions/eae672be-3f32-4eae-baf5-4c7e5335fec4

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

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
variable {L : Type} [Field L] (O : Subring L) {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (U : GL n L) (hU : U ∈ GLint n O) (i j : n) :
    (U : Matrix n n L) i j ∈ O := by
  obtain ⟨V, rfl⟩ := hU
  exact ((V : Matrix n n O) i j).2
end Formalism.UG.P
