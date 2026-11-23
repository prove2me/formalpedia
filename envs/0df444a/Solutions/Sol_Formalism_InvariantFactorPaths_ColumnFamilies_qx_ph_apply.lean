-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qx_ph_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:09.868616+00:00
-- url     : https://prove2.me/submissions/a2f8ae0b-7759-42ee-9a34-db30ef57a9b4

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
variable {M M' : GLMod n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) (x : qx_J Str CF) (i : M'.ι)
    (I : TIdx (x.2 : Fin n → ℤ)) :
    qx_ph ps e CF x i I = ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
