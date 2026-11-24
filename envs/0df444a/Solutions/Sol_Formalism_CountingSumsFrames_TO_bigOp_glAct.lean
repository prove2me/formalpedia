-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.bigOp_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:48.218748+00:00
-- url     : https://prove2.me/submissions/c14341d3-1fcc-462d-9a68-581ad533cc08

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_isF
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_glAct

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
theorem _root_.solution (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    bigOp L j0 Pi φ (glAct p L j0 c d x) = glAct p L j0 c d (bigOp L j0 Pi φ x) := by
  exact ext_glAct L le_rfl _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_isF L j0 e J M Pi φ hPi hφ) c d x
end Formalism.CountingSumsFrames.TO
