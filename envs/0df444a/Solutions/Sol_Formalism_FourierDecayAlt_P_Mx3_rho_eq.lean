-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:56.820966+00:00
-- url     : https://prove2.me/submissions/634b37cd-a953-4941-890f-833932c1a3ea

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
theorem _root_.solution (P : Par) (π : Ty P) (i : ℕ) (h : 1 ≤ i ∧ i ≤ P.k - 1) :
    rho P π i = P.lo i + (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) := by
  simp only [rho, dif_pos h]
end Formalism.FourierDecayAlt.P.Mx3
