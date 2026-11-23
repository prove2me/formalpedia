-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:21.074076+00:00
-- url     : https://prove2.me/submissions/5d987356-683b-40fe-a69a-268f91facaad

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_eta_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Finset Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (_hi : 1 ≤ i) :
    1 - (q : ℝ) ^ (-i) ≤ 1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) ∧
      1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) ≤ 1 + (q : ℝ) ^ (-i) := by
  have hpos : 0 < (q : ℝ) ^ (-i) := zpow_pos (by exact_mod_cast (by omega : 0 < q)) _
  rcases eta_pow η hη i with h | h <;> rw [h] <;> constructor <;> linarith
end Formalism.FourierDecayAlt.P.S3x5
