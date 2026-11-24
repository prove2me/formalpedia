-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.dg_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:38.608693+00:00
-- url     : https://prove2.me/submissions/d1ff0425-bb57-40ec-afad-d7a51cf50e55

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial


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
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}
omit [CharZero K] [Fintype L] [NeZero r]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg f F = ∑ α ∈ F.support, monomial α (f α * F.coeff α) := by
  conv_lhs => rw [F.as_sum, map_sum]
  exact Finset.sum_congr rfl fun α _ => dg_monomial f α _
end Formalism.MainNotions.PlaneGram
