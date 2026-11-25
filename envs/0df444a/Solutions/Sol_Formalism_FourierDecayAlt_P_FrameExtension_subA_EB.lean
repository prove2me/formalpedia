-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameExtension.subA_EB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:21:53.237506+00:00
-- url     : https://prove2.me/submissions/a8da726a-ed1b-41f3-b899-283cb3fe19f7

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameExtension
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.FrameExtension
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {k r m : ℕ} (π : Mx k r → (W →L[ℂ] W))
    (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (e : Fin (2 * r + k + 1) → ℂ) :
    subA (EB π (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e)) = EB π Bs := by
  funext a b
  simp [subA, EB, unitB, Fin.snoc_castSucc]
end Formalism.FourierDecayAlt.P.FrameExtension
