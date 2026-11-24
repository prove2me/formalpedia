-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.min_add_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:52:13.56319+00:00
-- url     : https://prove2.me/submissions/646ba25a-1f90-49e9-a651-12d3978eda1b

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution {t : ℕ} (a b : Fin t) : ((min a b : Fin t) : ℕ) + ((max a b : Fin t) : ℕ) = (a : ℕ) + (b : ℕ) := by
  rw [Fin.coe_min, Fin.coe_max]; omega
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
