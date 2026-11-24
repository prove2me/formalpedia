-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.bigOp_Y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:49.889531+00:00
-- url     : https://prove2.me/submissions/554d5fb7-adbd-4a3c-a1ed-16489de4863b

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_Y
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_mem
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_wh

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
theorem _root_.solution : ∀ y ∈ Y p L J M, bigOp L j0 Pi φ y ∈ Y p L J M := by
  exact ext_Y L j0 J M _ (inOp_glAct L j0 e J M Pi φ hPi hφ) (inOp_wh L j0 e J M Pi φ hPi hφ)
    (fun x => (Submodule.mem_inf.mp (inOp_mem L j0 e J M Pi φ hPi hφ x)).1)
    (fun x _ => inOp_mem L j0 e J M Pi φ hPi hφ x)
end Formalism.CountingSumsFrames.TO
