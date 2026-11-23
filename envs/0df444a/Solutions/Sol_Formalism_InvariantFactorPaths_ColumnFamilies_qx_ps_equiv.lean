-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qx_ps_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:10.125724+00:00
-- url     : https://prove2.me/submissions/871eebba-d19b-4a66-a2b1-6250d37b27ee

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (I : TIdx nu) :
    ∑ y : TIdx mu × κ, TMat mu K y.1 * B k y.2 * (ps mu nu y I : GLCoord ℤ n) =
      ∑ I', (ps mu nu (K, k) I' : GLCoord ℤ n) * TMat nu I' I :=
  congrFun (congrFun (hd.2.2.2.1 mu hmu nu hnu) (K, k)) I
end Formalism.InvariantFactorPaths.ColumnFamilies
