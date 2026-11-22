-- Prove2me | solution 1 for Formalism.G0.DetValP.prod_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:45.463194+00:00
-- url     : https://prove2.me/submissions/ef9f88dc-96c9-481e-8027-76141c3ba191

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetValP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetValP
theorem _root_.solution {L : Type} [Field L] {r : ℕ} (hr : 1 ≤ r) :
    ∏ a : Fin r, (if a.val + 1 = r then (Polynomial.X : Polynomial L) else 1) = Polynomial.X := by
  rw [Finset.prod_eq_single (⟨r - 1, by omega⟩ : Fin r)]
  · simp; omega
  · intro b _ hb
    have : b.val + 1 ≠ r := by
      intro h; apply hb; ext; simp; omega
    simp [this]
  · simp
end Formalism.G0.DetValP
