-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.weight_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:27.99387+00:00
-- url     : https://prove2.me/submissions/b70bae69-b764-4bd3-8819-461a1fcec4c1

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {σ : Type} (w : σ → ℤ) (hw : ∀ v, 0 ≤ w v) (m : σ →₀ ℕ) :
    Finsupp.weight w m = 0 ↔ ∀ v, m v ≠ 0 → w v = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg (fun v _ => nsmul_nonneg (hw v) _)]
  constructor
  · intro h v hv
    have := h v (Finsupp.mem_support_iff.mpr hv)
    rw [nsmul_eq_mul] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by exact_mod_cast h0 : m v = 0) hv
    · exact h0
  · intro h v hv
    rw [h v (Finsupp.mem_support_iff.mp hv), smul_zero]
end Formalism.CountingSumsFrames.TO
