-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.hpk_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:18.78723+00:00
-- url     : https://prove2.me/submissions/715dbf40-6cea-4d2b-8aba-33e1645dbf4a

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
end Formalism.FourierDecayAlt.P.Ux3
