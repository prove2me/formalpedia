-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.herm_smul_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:43.316138+00:00
-- url     : https://prove2.me/submissions/572fdc9c-0a5a-4886-826e-55601d83c805

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
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (a w : Fin n → ℂ) :
    herm H (s • a) w = s * herm H a w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]
end Formalism.FourierDecayAlt.P.HermitianXiVector
