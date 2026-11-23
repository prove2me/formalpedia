-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.floor_of_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:27.379406+00:00
-- url     : https://prove2.me/submissions/dd3dc63f-ced3-4d00-bfce-b2f1d3a4d68c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (x : ℝ) (h0 : 0 ≤ x) (z : ℤ) (hz : x = z) : ((⌊x⌋₊ : ℕ) : ℝ) = x := by
  have hz0 : 0 ≤ z := by have : (0 : ℝ) ≤ (z : ℝ) := hz ▸ h0; exact_mod_cast this
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  rw [hz]; simp
end Formalism.FourierDecayAlt.P.Mx4
