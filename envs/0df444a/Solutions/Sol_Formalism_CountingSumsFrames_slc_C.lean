-- Prove2me | solution 1 for Formalism.CountingSumsFrames.slc_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:07.661439+00:00
-- url     : https://prove2.me/submissions/c0ba3299-f3b6-4ab9-9a20-ac3a5e8ad3ad

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_slc_ycond
import Theorems.Thm_Formalism_CountingSumsFrames_slc_pol
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
theorem _root_.solution [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Y p L J M) (m : Fin N × Fin r →₀ ℕ) :
    slc (fsj N r j0) m x ∈ Cset p L j0 J M := by
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨slc_pol L j0 m hxP, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  by_cases hk : J k < j0
  · rw [Mup, if_pos hk]
    exact slc_ycond L (le_of_lt hk) (M k) m ((Submodule.mem_iInf _).mp hxY k)
  · rw [Mup, if_neg hk, ycond_top]; exact Submodule.mem_top
end Formalism.CountingSumsFrames
