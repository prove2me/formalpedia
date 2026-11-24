-- Prove2me | solution 1 for Formalism.CountingSumsFrames.midAct_mul_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:46.988238+00:00
-- url     : https://prove2.me/submissions/783e08c7-b22f-4da6-b83e-516b70fa0e77

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_midAct_isF
import Theorems.Thm_Formalism_CountingSumsFrames_midAct_eq
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul


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
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) {g q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : midAct p L j0 J c d (g * q) = g * midAct p L j0 J c d q := by
  have h0 := midAct_isF L j0 J c d hg
  rw [midAct_eq L hJ] at h0 ⊢
  rw [midAct_eq L hJ c d q, Formalism.GM.M.FB.glAct_mul, Formalism.GM.M.FB.glAct_mul]
  have : q * glAct p L J c d g - q * glAct p L j0 c d g = 0 := by rw [← mul_sub, h0, mul_zero]
  linear_combination this
end Formalism.CountingSumsFrames
