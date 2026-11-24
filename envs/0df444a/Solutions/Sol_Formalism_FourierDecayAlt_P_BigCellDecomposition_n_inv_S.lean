-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellDecomposition.n_inv_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:41:04.498275+00:00
-- url     : https://prove2.me/submissions/5964e117-3484-4d7f-9e92-f658e7ba5f10

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellZetaMinors_one_uw
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellDecomposition
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.BigCellDecomposition
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw z, n⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn, (one_mul _).symm⟩
end Formalism.FourierDecayAlt.P.BigCellDecomposition
