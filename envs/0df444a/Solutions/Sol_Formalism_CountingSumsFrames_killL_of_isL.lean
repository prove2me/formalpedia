-- Prove2me | solution 1 for Formalism.CountingSumsFrames.killL_of_isL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:18.843801+00:00
-- url     : https://prove2.me/submissions/dd293394-cea1-4cb8-aef4-1596863dd142

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
theorem _root_.solution {j0 J : ℕ} (hJ : J ≤ j0) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hq : IsL (fsj N r j0) q) :
    ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < J → m v = 0 := by
  intro m hm v hv
  by_contra h
  exact hq m hm v h (by unfold fsj; omega)
end Formalism.CountingSumsFrames
