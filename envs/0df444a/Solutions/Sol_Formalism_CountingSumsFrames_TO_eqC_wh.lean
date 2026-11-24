-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.eqC_wh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:53.412179+00:00
-- url     : https://prove2.me/submissions/013e99b8-68a4-4b03-8702-c2c783618d1c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_isWt_of_eig
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isWt_iff_wh
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_diag_of_isWt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)
include hPi
include hφ
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (ν : Fin r → ℤ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Cset p L j0 J M)
    (hw : y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) :
    φ y ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν := by
  rw [← isWt_iff_wh] at hw ⊢
  refine GlX.isWt_of_eig (GA p L j0) fun c => ?_
  have h1 : glAct p L j0 c c y = ((ν c : ℤ) : ℚ_[p]) • y := (GA p L j0).E_diag_of_isWt hw c
  show glAct p L j0 c c (φ y) = _
  rw [← hφ.comm y hy, h1, map_smul]
end Formalism.CountingSumsFrames.TO
