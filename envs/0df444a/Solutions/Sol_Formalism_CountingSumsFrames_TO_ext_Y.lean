-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.ext_Y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:35.812802+00:00
-- url     : https://prove2.me/submissions/b8c52fe3-2102-4341-bd8c-145b7d085c38

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_eq_sum
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isL_monomial_ltr
import Theorems.Thm_Formalism_CountingSumsFrames_TO_killL_of_isL
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isF_of_polLz
import Theorems.Thm_Formalism_CountingSumsFrames_TO_mul_ltr_pol
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_wh
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_C
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_mul_B
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_of_comm


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
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ1 : ∀ c d x, φ (glAct p L j0 c d x) = glAct p L j0 c d (φ x))
    (hφw : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν → φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν)
    (hφP : ∀ x, φ x ∈ Pol p r (Lz L j0)) (hφC : ∀ x ∈ Cset p L j0 J M, φ x ∈ Cset p L j0 J M) :
    ∀ x ∈ Y p L J M, ext (fsj N r j0) φ x ∈ Y p L J M := by
  classical
  intro x hx
  obtain ⟨hxP, hxY⟩ := Submodule.mem_inf.mp hx
  have hφF : ∀ x, IsF (fsj N r j0) (φ x) := fun x => isF_of_polLz L j0 (hφP x)
  have hsum := ext_eq_sum (fsj N r j0) φ x (x.support.image (ltr (fsj N r j0)))
    (fun m hm => Finset.mem_image_of_mem _ hm)
  refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_iInf _).mpr fun k => ?_⟩
  · rw [hsum]
    refine Submodule.sum_mem _ fun m hm => ?_
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
    exact mul_ltr_pol L j0 (hφP _) (((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hxP) hm')
  · by_cases hk : J k < j0
    · rw [hsum]
      refine Submodule.sum_mem _ fun m hm => ?_
      obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
      have h1 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp (hφC _ (slc_C L j0 J M hx (ltr (fsj N r j0) m')))).2 k
      rw [Mup, if_pos hk] at h1
      rw [mul_comm]
      exact ycond_mul_B L (le_of_lt hk) (M k) (killL_of_isL le_rfl (isL_monomial_ltr _ m' 1)) _ h1
    · have hJ : j0 ≤ J k := by omega
      exact ycond_of_comm L (J k) (M k) (ext (fsj N r j0) φ) (ext_glAct L hJ φ hφ1 hφF)
        (fun ν F hF => ext_wh L hJ φ hφw hφF ν F hF) x ((Submodule.mem_iInf _).mp hxY k)
end Formalism.CountingSumsFrames.TO
