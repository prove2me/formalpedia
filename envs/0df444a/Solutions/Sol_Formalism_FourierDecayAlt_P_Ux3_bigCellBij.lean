-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.bigCellBij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:12.15163+00:00
-- url     : https://prove2.me/submissions/ebe9aa7c-f3aa-4173-8ad4-9970405b3356

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_bigCell_uniq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_bigCell_exists

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
theorem _root_.solution : BigCellBij := by
  intro k j ρ g hg hD
  obtain ⟨x, x', Z, γ, hZ, hγ, hgeq⟩ := bigCell_exists g hg hD
  refine ⟨((x, x'), (Z, γ)), ⟨hZ, hγ, hgeq⟩, ?_⟩
  rintro ⟨⟨y, y'⟩, ⟨Z', γ'⟩⟩ ⟨hZ', hγ', hgeq'⟩
  obtain ⟨h1, h2, h3, h4⟩ := bigCell_uniq y y' x x' Z' Z γ' γ hZ' hZ hγ (hgeq'.symm.trans hgeq)
  simp only [h1, h2, h3, h4]
end Formalism.FourierDecayAlt.P.Ux3
