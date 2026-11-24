-- Prove2me | solution 1 for Formalism.L2.LamCM.le_one_of_count_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:37.660637+00:00
-- url     : https://prove2.me/submissions/24d63cd0-f7a1-460e-8c6a-d8f8ca873a85

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Theorems.Thm_Formalism_L2_LamCM_le_one_mul

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
theorem _root_.solution {J : FractionalIdeal (𝓞 K)⁰ K} (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K v J) : J ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  refine finprod_induction (· ≤ 1) le_rfl (fun a b ha hb => le_one_mul ha hb) (fun v => ?_)
  show (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v J ≤ 1
  rw [← Int.toNat_of_nonneg (h v), zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one
end Formalism.L2.LamCM
