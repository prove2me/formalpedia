-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Herglotz.fac_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:00.464567+00:00
-- url     : https://prove2.me/submissions/c1943a1e-50b5-4f8d-ab16-3b94201d4d07

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Herglotz
open Real Filter Topology Finset
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.Herglotz
theorem _root_.solution (N : ℕ) (t : ℤ) : fac N t ≤ 1 := by
  unfold fac
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]
    have : ((N : ℤ) - |t|).toNat ≤ N := by
      have := abs_nonneg t
      omega
    exact_mod_cast this
end Formalism.FourierDecayAlt.P.Herglotz
