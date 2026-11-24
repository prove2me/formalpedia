-- Prove2me | solution 1 for Formalism.L2.LamCM.le_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:23.355556+00:00
-- url     : https://prove2.me/submissions/2bbc5b51-95f1-432f-a98d-e440545c0fa1

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne

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
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution {A B : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≤ 1) (hB : B ≤ 1) : A * B ≤ 1 := by
  obtain ⟨A0, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hA
  obtain ⟨B0, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hB
  rw [← FractionalIdeal.coeIdeal_mul]
  exact FractionalIdeal.coeIdeal_le_one
end Formalism.L2.LamCM
