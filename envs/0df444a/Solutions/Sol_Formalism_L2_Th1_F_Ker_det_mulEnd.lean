-- Prove2me | solution 1 for Formalism.L2.Th1.F.Ker.det_mulEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:25:00.717863+00:00
-- url     : https://prove2.me/submissions/2663ef35-138b-44ce-8cdc-b4286c91acf5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Theorems.Thm_Formalism_L2_Th1_F_Ker_matrix_data

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Ker
namespace Formalism.L2.Th1.F.Ker
theorem _root_.solution (L : PeriodPair) (α : ℂ) (h : MulStable L α) :
    ((LinearMap.det (mulEnd L α h) : ℤ) : ℝ) = Complex.normSq α := by
  obtain ⟨a, b, c, d, hac, hbd, -, hn⟩ := matrix_data L α h
  have h0 : mulEnd L α h (L.latticeBasis 0) = a • L.latticeBasis 0 + c • L.latticeBasis 1 := by
    apply Subtype.ext
    simp [mulEnd, L.latticeBasis_zero, L.latticeBasis_one, hac]
  have h1 : mulEnd L α h (L.latticeBasis 1) = b • L.latticeBasis 0 + d • L.latticeBasis 1 := by
    apply Subtype.ext
    simp [mulEnd, L.latticeBasis_zero, L.latticeBasis_one, hbd]
  have key : LinearMap.det (mulEnd L α h) = a * d - b * c := by
    rw [← LinearMap.det_toMatrix L.latticeBasis, Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, h0, h1] <;> ring
  rw [hn, key]
end Formalism.L2.Th1.F.Ker
