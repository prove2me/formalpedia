-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.rn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:02.718979+00:00
-- url     : https://prove2.me/submissions/2913b808-b74d-4e60-a04e-6063c246479c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul

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
theorem _root_.solution (x : RC k j ρ) : Rn k j ρ x = blk3 1 (-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ))
    (G.wMat j * ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2))
    0 1 (Matrix.of x.1) 0 0 1 := rfl
end Formalism.FourierDecayAlt.P.Ux3
