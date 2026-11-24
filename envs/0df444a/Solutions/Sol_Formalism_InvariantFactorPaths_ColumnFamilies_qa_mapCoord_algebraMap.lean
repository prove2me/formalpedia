-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_mapCoord_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:42:48.298631+00:00
-- url     : https://prove2.me/submissions/1b4c992c-e1ba-4d60-b917-4a099ae72971

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


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
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} (F : Type) [CommRing F] (f : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) F (algebraMap _ (GLCoord ℤ n) f) =
      algebraMap _ (GLCoord F n) (MvPolynomial.map (Int.castRingHom F) f) := by
  unfold mapCoord
  rw [IsLocalization.Away.lift_eq]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
