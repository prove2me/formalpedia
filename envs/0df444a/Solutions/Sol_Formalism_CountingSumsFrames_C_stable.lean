-- Prove2me | solution 1 for Formalism.CountingSumsFrames.C_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:57.640225+00:00
-- url     : https://prove2.me/submissions/9ac2a980-6370-4a7b-bee6-946936948e01

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_glAct_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_top


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
theorem _root_.solution [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    (GA p (r := r) L j0).Stable (Cset p L j0 J M) := by
  intro c d x hx
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨pol_stable L (Lz L j0) j0 c d x hxP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  have h1 := (Submodule.mem_iInf _).mp hxY k
  by_cases hk : J k < j0
  · rw [Mup, if_pos hk] at h1 ⊢
    exact ycond_glAct_le L (le_of_lt hk) (M k) c d h1
  · rw [Mup, if_neg hk, ycond_top]; exact Submodule.mem_top
end Formalism.CountingSumsFrames
