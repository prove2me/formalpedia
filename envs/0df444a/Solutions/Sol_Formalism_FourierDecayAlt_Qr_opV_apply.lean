-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Qr.opV_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:18.770428+00:00
-- url     : https://prove2.me/submissions/0cdc5985-66b6-4cf2-97ad-312175d5a0bf

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_StatementQr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {k r i D E}
namespace Formalism.FourierDecayAlt.Qr
theorem _root_.solution (hD : IsOpen D) {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r i D T) (φ : SV k r i D E)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : (opV k r i D T φ).1 g = T φ.1 g := by
  rw [opV, dif_pos (show IsOpen D ∧ Qx2.Good k r i D T from ⟨hD, hT⟩)]
  exact cutF_of_mem hg
end Formalism.FourierDecayAlt.Qr
