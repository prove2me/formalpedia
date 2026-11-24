-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.Rep.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:12:54.62163+00:00
-- url     : https://prove2.me/submissions/f77a0d7f-ee8a-4949-aee5-3b6e09750b67

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.OperatorRepresentations
namespace Rep
theorem _root_.solution {X Y : Module.End ℂ (SV k r i D E)} {T S : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (hY : Rep Y S) :
    Rep (X * Y) (fun f => T (S f)) :=
  ⟨hX.1.comp hY.1, fun φ g hg => by
    show (X (Y φ)).1 g = T (S φ.1) g
    rw [hX.2 _ g hg]
    exact hX.1.loc _ _ (fun x hx => hY.2 φ x hx) g hg⟩
end Rep
end Formalism.FourierDecayAlt.P.OperatorRepresentations
