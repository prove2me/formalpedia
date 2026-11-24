-- Prove2me | solution 1 for Formalism.CountingSumsFrames.weight_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:55.243037+00:00
-- url     : https://prove2.me/submissions/3412ac36-6cc5-4a17-b353-a49ea50f4191

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution {σ : Type} (w : σ → ℤ) (hw : ∀ v, 0 ≤ w v) (m : σ →₀ ℕ) :
    Finsupp.weight w m = 0 ↔ ∀ v, m v ≠ 0 → w v = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg (fun v _ => nsmul_nonneg (hw v) _)]
  constructor
  · intro h v hv
    have e := h v (Finsupp.mem_support_iff.mpr hv)
    rcases smul_eq_zero.mp e with h1 | h1
    · exact absurd h1 hv
    · exact h1
  · intro h v hv
    rw [h v (Finsupp.mem_support_iff.mp hv), smul_zero]
end Formalism.CountingSumsFrames
