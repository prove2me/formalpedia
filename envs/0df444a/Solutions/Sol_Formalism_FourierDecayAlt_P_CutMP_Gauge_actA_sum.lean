-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.actA_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:09.927024+00:00
-- url     : https://prove2.me/submissions/1f26219f-7d9e-4d4d-9c0e-062d72129903

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_actA_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_actA_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge
noncomputable section
variable (P : M.Par)
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge
theorem _root_.solution {ι : Type} (s : Finset ι) (x : ι → MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (∑ i ∈ s, x i) f = ∑ i ∈ s, MA.actA P (x i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, actA_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, actA_add, ih]
end Formalism.FourierDecayAlt.P.CutMP.Gauge
