-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.herm_smul_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:47:54.535076+00:00
-- url     : https://prove2.me/submissions/7e315502-2595-414b-9ece-3be68c48285b

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
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (v a : Fin n → ℂ) :
    herm H v (s • a) = conj s * herm H v a := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
  try rfl
end Formalism.FourierDecayAlt.P.HermitianXiVector
