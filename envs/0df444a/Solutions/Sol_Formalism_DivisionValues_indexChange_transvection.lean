-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:54:52.70932+00:00
-- url     : https://prove2.me/submissions/0f9686b0-c6cb-4f45-b20d-21405cbc5b2e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_indexChange_one
import Theorems.Thm_Formalism_DivisionValues_indexChange_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_det_Dg
import Theorems.Thm_Formalism_DivisionValues_indexChange_scalar
import Theorems.Thm_Formalism_DivisionValues_indexChangeLocal_transvection
import Theorems.Thm_Formalism_DivisionValues_idxChange_transvection_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (v : HeightOneSpectrum R) (t : Matrix.TransvectionStruct (Fin d) K) :
    IdxChangeP v t.toMatrix := by
  rcases t with ⟨i, j, hij, c⟩
  rw [Matrix.TransvectionStruct.toMatrix_mk]
  by_cases hc : c = 0
  · subst hc
    rw [Matrix.transvection_zero]
    exact indexChange_one v
  rw [idxChange_transvection_conj hij hc]
  have hd1 : (idxChangeDg i c).det ≠ 0 := by rw [idxChange_det_Dg]; exact hc
  have hd2 : (Matrix.transvection i j (1 : K)).det ≠ 0 := by
    rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero
  have hd3 : (idxChangeDg i c⁻¹).det ≠ 0 := by rw [idxChange_det_Dg]; exact inv_ne_zero hc
  refine indexChange_mul v (by rw [Matrix.det_mul]; exact mul_ne_zero hd1 hd2) hd3
    (indexChange_mul v hd1 hd2 (indexChange_scalar v i hc) (indexChangeLocal_transvection v hij))
    (indexChange_scalar v i (inv_ne_zero hc))
end Formalism.DivisionValues
