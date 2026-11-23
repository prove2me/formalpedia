-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.floor_of_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:20.902915+00:00
-- url     : https://prove2.me/submissions/f5191729-30e3-4cee-a105-419bf473ab82

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution (x : ℝ) (h0 : 0 ≤ x) (z : ℤ) (hz : x = z) : ((⌊x⌋₊ : ℕ) : ℝ) = x := by
  have hz0 : 0 ≤ z := by have : (0 : ℝ) ≤ (z : ℝ) := hz ▸ h0; exact_mod_cast this
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  rw [hz]; simp
end Formalism.FourierDecayAlt.P.Mx3
