-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.radicalParam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:12.528129+00:00
-- url     : https://prove2.me/submissions/69175a44-150a-4ddf-a3e1-eb624253fdb6

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_rset_sub_nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_rn_rset
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_rn_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_rset_sub_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution : RadicalParam := by
  intro k j ρ
  refine ⟨rn_injective, ?_, rset_sub_nset⟩
  ext g
  constructor
  · rintro ⟨x, rfl⟩; exact rn_rset x
  · intro hg; exact rset_sub_range hg
end Formalism.FourierDecayAlt.P.Ux2
