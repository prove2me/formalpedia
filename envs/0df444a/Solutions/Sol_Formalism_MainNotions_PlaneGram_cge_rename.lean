-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:45.294919+00:00
-- url     : https://prove2.me/submissions/8c5bf71c-e001-44a5-ba90-c65c6dbb5fa2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero


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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (v : AddValuation K (WithTop ℚ)) {σ τ : Type} (f : σ → τ) (hf : Function.Injective f)
    {a : ℝ} {Q : MvPolynomial σ K} (hQ : cge v a Q) : cge v a (rename f Q) := by
  intro β
  by_cases h : ∃ u : σ →₀ ℕ, u.mapDomain f = β
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain f hf]
    exact hQ u
  · rw [coeff_rename_eq_zero f Q β (fun u hu => absurd ⟨u, hu⟩ h)]
    exact vge_zero v a
end Formalism.MainNotions.PlaneGram
