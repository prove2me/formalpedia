-- Prove2me | solution 1 for Formalism.Q3.CMRootsOfUnity.not_dvd_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:29.901709+00:00
-- url     : https://prove2.me/submissions/b0cfab09-3ea0-494f-88a3-67896d2c4172

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMRootsOfUnity
variable {q : Fin 3 → ℕ}
namespace Formalism.Q3.CMRootsOfUnity
theorem _root_.solution (hq : Hyp3 q) (i : Fin 3) : ¬ (q i : ℤ) ∣ 1 := by
  intro h
  have h1 : q i ∣ 1 := by exact_mod_cast h
  exact (hq.1 i).1.one_lt.ne' (Nat.dvd_one.1 h1)
end Formalism.Q3.CMRootsOfUnity
