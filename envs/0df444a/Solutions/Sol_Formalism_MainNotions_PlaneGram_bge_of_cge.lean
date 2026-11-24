-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.bge_of_cge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:21:25.638488+00:00
-- url     : https://prove2.me/submissions/c01a8751-306a-4f94-b424-612b7f42a82f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_lower

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ} {d : L → ℕ} {a : ℝ}
    {F : MvPolynomial (L × Fin r) K} (hF : F ∈ PolK K r d) (h : cge v a F) :
    bge v (a + (vN v (∏ i, (d i).factorial) - kapL p r d) / 2) F := by
  intro α
  by_cases h0 : F.coeff α = 0
  · rw [h0]
    exact vge_zero v _
  · have hα : ∀ i, ldeg α i = d i := by
      unfold PolK at hF
      rw [MvPolynomial.mem_restrictSupport_iff] at hF
      exact hF (MvPolynomial.mem_support_iff.mpr h0)
    have hl := fact_lower hD hα
    refine vge_mono v ?_ (h α)
    linarith
end Formalism.MainNotions.PlaneGram
