-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:35.168364+00:00
-- url     : https://prove2.me/submissions/8d222c15-1adc-4f9b-9d03-8b39854c9f5c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R')
    (P : MvPolynomial (Fin n × Fin n) R) :
    evGLR g (algebraMap _ (GLCoord R n) P) =
      MvPolynomial.eval₂Hom (algebraMap R R') (fun ab : Fin n × Fin n => g.val ab.1 ab.2) P := by
  unfold evGLR
  exact IsLocalization.Away.lift_eq _ _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
