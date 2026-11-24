-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.slc_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:27.555791+00:00
-- url     : https://prove2.me/submissions/c91bcbab-a5c2-4be9-84fd-a7417d3a180c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_ycond
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_pol
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_top
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_top


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
theorem _root_.solution [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Y p L J M) (m : Fin N × Fin r →₀ ℕ) :
    slc (fsj N r j0) m x ∈ Cset p L j0 J M := by
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨slc_pol L j0 m hxP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  by_cases hk : J k < j0
  · rw [Mup, if_pos hk]
    exact slc_ycond L (le_of_lt hk) (M k) m ((Submodule.mem_iInf _).mp hxY k)
  · rw [Mup, if_neg hk, ycond_top]; exact Submodule.mem_top
end Formalism.CountingSumsFrames.TO
