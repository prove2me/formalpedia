-- Prove2me | solution 1 for Formalism.L2.LamCM.dot_basis_vector_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:13:33.679022+00:00
-- url     : https://prove2.me/submissions/12891503-e8c5-4456-b42c-e8c7897781ff

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_HermitianFormGramBlockBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain IsLocalRing Matrix
open scoped nonZeroDivisors ComplexOrder
namespace Formalism.L2.LamCM
theorem _root_.solution {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (j : Fin k) :
    star ((1 : Matrix (Fin k) (Fin k) ℂ) j) ⬝ᵥ (M *ᵥ (1 : Matrix (Fin k) (Fin k) ℂ) j) = M j j := by
  simp [dotProduct, mulVec, Matrix.one_apply]
end Formalism.L2.LamCM
