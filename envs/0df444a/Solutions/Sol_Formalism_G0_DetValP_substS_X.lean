-- Prove2me | solution 1 for Formalism.G0.DetValP.substS_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:01.942559+00:00
-- url     : https://prove2.me/submissions/dc1b8ee3-c889-4f75-b755-aa693c5f04f6

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
theorem _root_.solution {L : Type} [Field L] [Algebra K L] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (g : GL (Fin r) L) (p : ι × Fin r) :
    substS (K := K) vec S g (MvPolynomial.X p) =
      (if p.1 ∈ S then
      (if vec p.1 then ∑ b, MvPolynomial.C ((msMat g) p.2 b) * MvPolynomial.X (p.1, b)
       else ∑ b, MvPolynomial.C ((msDualMat g) p.2 b) * MvPolynomial.X (p.1, b))
    else MvPolynomial.X p) := by
  simp [substS]
end Formalism.G0.DetValP
