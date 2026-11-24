-- Prove2me | solution 1 for Formalism.SA.P.sqrt_absNorm_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:46.424486+00:00
-- url     : https://prove2.me/submissions/d8404eb0-d0e6-4b4d-ba8c-8cf60d9a0c23

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
import Theorems.Thm_Formalism_SA_P_absNorm_le_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
namespace Formalism.SA.P
theorem _root_.solution (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    √(FractionalIdeal.absNorm b : ℝ) ≤ ∏ w : InfinitePlace E, w l := by
  have h1 := absNorm_le_norm b hb l hl hl0
  have h2 : |((Algebra.norm ℚ l : ℚ) : ℝ)| = (∏ w : InfinitePlace E, w l) ^ 2 := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hw : w.mult = 2 :=
      NumberField.InfinitePlace.mult_isComplex ⟨w, NumberField.IsTotallyComplex.isComplex w⟩
    rw [hw]
  have hP : 0 ≤ ∏ w : InfinitePlace E, w l :=
    Finset.prod_nonneg fun w _ => (NumberField.InfinitePlace.pos_iff.mpr hl0).le
  rw [h2] at h1
  calc √(FractionalIdeal.absNorm b : ℝ) ≤ √((∏ w : InfinitePlace E, w l) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ∏ w : InfinitePlace E, w l := Real.sqrt_sq hP
end Formalism.SA.P
