-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.bigOp_slc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:46.241799+00:00
-- url     : https://prove2.me/submissions/6fb8fe74-18d3-4e52-a4d8-e0ad0575ee1c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_slc_ext
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_isF

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
theorem _root_.solution (m : Fin N × Fin r →₀ ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    slc (fsj N r j0) m (bigOp L j0 Pi φ x) = inOp L j0 Pi φ (slc (fsj N r j0) m x) := by
  exact slc_ext _ _ (inOp_isF L j0 e J M Pi φ hPi hφ) m x
end Formalism.CountingSumsFrames.TO
