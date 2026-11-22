-- Prove2me | solution 1 for Formalism.G0.DetValP.substS_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:00.876947+00:00
-- url     : https://prove2.me/submissions/79152286-9b02-49f1-a17e-2a910abcb5b7

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
    (g : GL (Fin r) L) (A : Fin r → ι) {R : Type} [CommRing R]
    (φ : MvPolynomial (ι × Fin r) (Polynomial L) →+* R) :
    φ (substS (K := K) vec S g (detLetters A)) =
      Matrix.det (Matrix.of fun l a => φ (substS (K := K) vec S g (MvPolynomial.X (A l, a)))) := by
  unfold detLetters
  rw [AlgHom.map_det, RingHom.map_det]
  congr 1
end Formalism.G0.DetValP
