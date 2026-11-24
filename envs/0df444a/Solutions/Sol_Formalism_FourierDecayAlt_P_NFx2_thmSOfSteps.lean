-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.thmSOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:24:28.538352+00:00
-- url     : https://prove2.me/submissions/2c7a722e-ded4-4d99-84c6-f555ee00036b

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution : ThmSOfSteps := by
  intro hI hC hU hN hRP hW hB hSC hSN hRel P A _ _ _ L0 QQ κ hP h
  obtain ⟨b, SS, hF, hR, hSS⟩ := hB hI hC hU P A L0 QQ κ hP h
  obtain ⟨L, hExt, hnab, hnabs, hst, hcore, hqq⟩ := hSC P A L0 QQ κ b SS hP h hF hR hSS
  obtain ⟨hnorm, h11⟩ := hSN hI hC hU hN hRP hW P A L0 QQ κ b SS L hP h hF hR hSS hExt hnab hnabs hst hcore
    (fun Y => ⟨(hqq Y).1, (hqq Y).2.1⟩)
  refine ⟨⟨L, κ, SS⟩, hExt, rfl, hst, (hRel P A ⟨L, κ, SS⟩).2 ⟨hcore, hnorm⟩, fun Y => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · exact h11 Y
  · exact (hqq Y).2.1
  · exact (hqq Y).1
  · exact (hqq Y).2.2
end Formalism.FourierDecayAlt.P.NFx2
