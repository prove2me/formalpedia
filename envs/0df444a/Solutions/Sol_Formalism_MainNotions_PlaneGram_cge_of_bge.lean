-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_of_bge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:22:43.466055+00:00
-- url     : https://prove2.me/submissions/63ac3f78-6135-46b7-88e9-cdf548bed2ca

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_upper

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
    {F : MvPolynomial (L × Fin r) K} (hF : F ∈ PolK K r d) (h : bge v a F) :
    cge v (a - vN v (∏ i, (d i).factorial) / 2) F := by
  intro α
  by_cases h0 : F.coeff α = 0
  · rw [h0]
    exact vge_zero v _
  · have hα : ∀ i, ldeg α i = d i := by
      unfold PolK at hF
      rw [MvPolynomial.mem_restrictSupport_iff] at hF
      exact hF (MvPolynomial.mem_support_iff.mpr h0)
    have hu := fact_upper hD hα
    refine vge_mono v ?_ (h α)
    linarith
end Formalism.MainNotions.PlaneGram
