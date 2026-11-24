-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x6.E_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:06.881066+00:00
-- url     : https://prove2.me/submissions/6125752e-5df1-4617-8071-685d77238c79

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_E_cast

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
open Formalism.FourierDecayAlt.P.C2x6
open C2x5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x6
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) (v : Fin n → ℂ) :
    ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  apply Complex.ofReal_injective
  rw [← E_cast (H *ᵥ v), ← E_cast v, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.C2x6
