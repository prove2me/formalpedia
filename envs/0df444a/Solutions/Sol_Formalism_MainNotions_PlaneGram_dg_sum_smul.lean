-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.dg_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:16:58.17347+00:00
-- url     : https://prove2.me/submissions/9ac9fcb8-b0c8-44a2-a68f-e80001742a40

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_dg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ ι : Type} (s : Finset ι) (lam : ι → K) (b : ι → (σ →₀ ℕ) → K)
    (F : MvPolynomial σ K) :
    dg (fun α => ∑ k ∈ s, lam k * b k α) F = ∑ k ∈ s, lam k • dg (b k) F := by
  ext β
  simp only [coeff_dg, coeff_sum, coeff_smul, smul_eq_mul, Finset.sum_mul, mul_assoc]
end Formalism.MainNotions.PlaneGram
