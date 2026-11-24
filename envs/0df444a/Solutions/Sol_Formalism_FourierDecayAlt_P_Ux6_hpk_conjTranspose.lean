-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.hpk_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:02:24.364617+00:00
-- url     : https://prove2.me/submissions/f313853a-7b3d-44a0-b462-11d836b63319

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i b
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> (try simp) <;> omega
end Formalism.FourierDecayAlt.P.Ux6
