-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:37.949914+00:00
-- url     : https://prove2.me/submissions/1d9e6269-4093-4393-a9a3-df13d1d102fb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_one
import Theorems.Thm_Formalism_DivisionValues_idxChange_act_one
import Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_self

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
theorem _root_.solution (v : HeightOneSpectrum R) : IdxChangeP (d := d) v (1 : Matrix _ _ K) := by
  intro e he
  rw [idxChange_act_one, idxChange_lidx_self, Matrix.det_one, idxChange_cnt_one]
end Formalism.DivisionValues
