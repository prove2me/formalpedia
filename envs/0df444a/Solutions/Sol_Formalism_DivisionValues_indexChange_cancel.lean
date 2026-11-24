-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:25:40.383277+00:00
-- url     : https://prove2.me/submissions/db83aed3-e8ab-42bb-bf7d-35d08ffa08ea

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_act_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_linIndep_act
import Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_add
import Theorems.Thm_Formalism_DivisionValues_idxChange_det_Dg
import Theorems.Thm_Formalism_DivisionValues_idxChange_Dg_mul

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
theorem _root_.solution (v : HeightOneSpectrum R) (i : Fin d) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) (Px : IdxChangeP v (idxChangeDg i x)) (Pxy : IdxChangeP v (idxChangeDg i (x * y))) :
    IdxChangeP v (idxChangeDg i y) := by
  intro e he
  have hdy : (idxChangeDg i y).det ≠ 0 := by rw [idxChange_det_Dg]; exact hy
  have hdx : (idxChangeDg i x).det ≠ 0 := by rw [idxChange_det_Dg]; exact hx
  have hey := idxChange_linIndep_act he hdy
  have hadd := idxChange_lidx_add v.asIdeal he hey (idxChange_linIndep_act hey hdx)
  rw [Px _ hey, idxChange_act_mul, idxChange_Dg_mul, mul_comm y x, Pxy e he] at hadd
  rw [idxChange_det_Dg] at hadd ⊢
  rw [idxChange_det_Dg, idxChange_cnt_mul v hx hy] at hadd
  linarith
end Formalism.DivisionValues
