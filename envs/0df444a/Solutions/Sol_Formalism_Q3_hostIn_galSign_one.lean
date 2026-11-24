-- Prove2me | solution 1 for Formalism.Q3.hostIn_galSign_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:28.669113+00:00
-- url     : https://prove2.me/submissions/5faa82e3-0ffe-4bf4-9e4f-0ada9dcb7539

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution {E : Type} [Field E] [Algebra ℚ E] (α : Fin 3 → E) :
    galSign α (1 : Gal(E/ℚ)) = 1 := by
  funext j
  simp [galSign]
end Formalism.Q3
