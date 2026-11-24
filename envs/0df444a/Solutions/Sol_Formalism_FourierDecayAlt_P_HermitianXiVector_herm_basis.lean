-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.herm_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:01.661925+00:00
-- url     : https://prove2.me/submissions/5e8bbdad-bdbb-400c-8e16-c749103730ee

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianXiVector
theorem _root_.solution {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    herm H (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single i 1) = (Aᴴ * H * A) i j := by
  have e1 : herm H (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single i 1) =
      herm (Aᴴ * H * A) (Pi.single j 1) (Pi.single i 1) := by
    simp only [herm, star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]
  rw [e1]
  simp [herm, dotProduct, mulVec, Pi.single_apply]
end Formalism.FourierDecayAlt.P.HermitianXiVector
