-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:10:58.36351+00:00
-- url     : https://prove2.me/submissions/0e622649-18cf-4edc-9938-cb5f74ff2fb0

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_indexChange_mul
import Theorems.Thm_Formalism_DivisionValues_indexChange_diagonal
import Theorems.Thm_Formalism_DivisionValues_indexChange_transvection

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
theorem _root_.solution (v : HeightOneSpectrum R) (γ : Matrix (Fin d) (Fin d) K) (hγ : γ.det ≠ 0) :
    IdxChangeP v γ := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (IdxChangeP v) γ hγ ?_
    (indexChange_transvection v) (fun A B hA hB PA PB => indexChange_mul v hA hB PA PB)
  intro D hD
  refine indexChange_diagonal v D fun k => ?_
  rw [Matrix.det_diagonal] at hD
  exact Finset.prod_ne_zero_iff.mp hD k (Finset.mem_univ k)
end Formalism.DivisionValues
