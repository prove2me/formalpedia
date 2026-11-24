-- Prove2me | solution 1 for Formalism.G0.DetValP.entry_one_nmem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:37.18937+00:00
-- url     : https://prove2.me/submissions/240d0b85-4cab-46de-82d6-12373f1e8db9

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Theorems.Thm_Formalism_G0_DetValP_substS_X

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
theorem _root_.solution {R : Type} [CommRing R] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (φ : Polynomial K →+* R) (v : ι × Fin r → R) (i : ι) (hi : i ∉ S) (a : Fin r) :
    MvPolynomial.eval₂Hom φ v (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (i, a))) =
      v (i, a) := by
  rw [substS_X]
  simp [hi]
end Formalism.G0.DetValP
