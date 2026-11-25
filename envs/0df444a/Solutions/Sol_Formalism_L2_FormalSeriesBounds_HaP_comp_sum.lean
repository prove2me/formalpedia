-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.comp_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:58:22.004138+00:00
-- url     : https://prove2.me/submissions/903d9ee1-6627-460f-bb1c-d00b8a9dde74

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_coeff_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (lam : K →ₗ[ℚ] ℚ) {α : Type} (s : Finset α) (f : α → MvPolynomial σ K) :
    comp lam (∑ i ∈ s, f i) = ∑ i ∈ s, comp lam (f i) := by
  ext m
  simp only [coeff_comp, coeff_sum, map_sum]
end Formalism.L2.FormalSeriesBounds.HaP
