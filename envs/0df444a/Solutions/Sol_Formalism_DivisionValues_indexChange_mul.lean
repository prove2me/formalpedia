-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:15.553274+00:00
-- url     : https://prove2.me/submissions/64161ed7-6e14-4a71-84b1-09a098565eb6

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_act_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_linIndep_act
import Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_add

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
theorem _root_.solution (v : HeightOneSpectrum R) {A B : Matrix (Fin d) (Fin d) K}
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (PA : IdxChangeP v A) (PB : IdxChangeP v B) :
    IdxChangeP v (A * B) := by
  intro e he
  have heA := idxChange_linIndep_act he hA
  have hadd := idxChange_lidx_add v.asIdeal he heA (idxChange_linIndep_act heA hB)
  rw [PA e he, PB _ heA, idxChange_act_mul] at hadd
  rw [hadd, Matrix.det_mul, idxChange_cnt_mul v hA hB]
end Formalism.DivisionValues
