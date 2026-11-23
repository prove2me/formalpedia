-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggHpk_ee
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:37.755625+00:00
-- url     : https://prove2.me/submissions/629d616b-a368-42eb-af48-22f29a65b721

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (a b : Fin r) : Hpk k r (eI k r a) (eI k r b) = 0 := by
  have ha := a.isLt
  have hb := b.isLt
  unfold Hpk
  rw [if_neg (fun h => absurd h.2 (by change ¬ (a.val + b.val = 2 * r + k); omega)),
    if_neg (fun h => absurd h.2 (by change ¬ (a.val + b.val = 2 * r + k); omega)),
    if_neg (fun h => absurd h.1 (by change ¬ (r ≤ a.val); omega))]
end Formalism.QuantumDeterminants
