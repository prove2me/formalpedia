-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.actA_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:44.55689+00:00
-- url     : https://prove2.me/submissions/0a1c811e-4bd4-4051-9c25-ce18970e2453

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_fst_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_fst_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_op_sum_apply

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
theorem _root_.solution (x y : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (x * y) f = MA.actA P x (MA.actA P y f) := by
  funext π
  simp only [MA.actA, Matrix.mul_apply, fst_sum, fst_mul]
  have h1 : ∀ π'' : M.Ty P, (∑ j, (x π j).1 * (y j π'').1) (f π'') =
      ∑ j, (x π j).1 ((y j π'').1 (f π'')) := fun π'' =>
    op_sum_apply P Finset.univ (fun j => (x π j).1 * (y j π'').1) (f π'')
  have h2 : ∀ π' : M.Ty P, (x π π').1 (∑ π'', (y π' π'').1 (f π'')) =
      ∑ π'', (x π π').1 ((y π' π'').1 (f π'')) := fun π' => map_sum (x π π').1 _ _
  exact (Finset.sum_congr rfl fun π'' _ => h1 π'').trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun π' _ => (h2 π').symm))
end Formalism.FourierDecayAlt.P.CutMP.Gauge
