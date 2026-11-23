-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.lo_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:27.4658+00:00
-- url     : https://prove2.me/submissions/6cfad0e1-a50b-4548-8187-4c1f7db40845

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
theorem _root_.solution (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : ∃ n : ℤ, P.lo i - P.u 1 - 1 / 2 = n := by
  have h := Finset.mem_Icc.1 hi
  obtain ⟨a, ha⟩ := hP.int_u (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  obtain ⟨b, hb⟩ := hP.int_u' (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  unfold Par.lo
  rcases max_choice (P.u (i + 1)) (P.u' (i + 1)) with h | h
  · exact ⟨a, by rw [h]; linarith⟩
  · exact ⟨b, by rw [h]; linarith⟩
end Formalism.FourierDecayAlt.P.Mx4
