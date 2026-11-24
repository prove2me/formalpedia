-- Prove2me | solution 1 for Formalism.CountingSumsFrames.YYsp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:28.838213+00:00
-- url     : https://prove2.me/submissions/57fb8a3f-2751-45ec-b884-aa7db935fab0

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_gSpan_eq


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
theorem _root_.solution [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : Fin T.t → ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.YYsp p LL i ρ n f = YYs p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
      (T.Ffull p (LL.setTies T n) i ρ (n i) f) := by
  unfold TieData.YYsp YYs
  rw [gSpan_eq LL T n (T.pos i + 2) (T.Ffull p (LL.setTies T n) i ρ (n i) f)]
  rfl
end Formalism.CountingSumsFrames
