-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.xEx_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:56.033288+00:00
-- url     : https://prove2.me/submissions/73cf4715-8a90-412a-aa6a-53684430a217

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (π : Ty P) (u : ℂ) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hlj : j ≠ l) :
    xEx P {l} π u = (u + (rho P π j : ℂ)) * xEx P {l, j} π u := by
  have h1 : Icc 1 (P.k - 1) \ {l, j} = (Icc 1 (P.k - 1) \ {l}).erase j := by
    ext x; simp only [mem_sdiff, mem_insert, mem_singleton, mem_erase]; tauto
  have h2 : j ∈ Icc 1 (P.k - 1) \ {l} := by simp only [mem_sdiff, mem_singleton]; exact ⟨hj, hlj⟩
  rw [xEx, xEx, h1]
  exact (Finset.mul_prod_erase _ (fun i => u + (rho P π i : ℂ)) h2).symm
end Formalism.FourierDecayAlt.P.Mx6
