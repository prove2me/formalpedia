-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.invM_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:13:57.366021+00:00
-- url     : https://prove2.me/submissions/b610a097-f53c-4cda-9147-72dae54fcdbe

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_inv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution {k r : ℕ} : Measurable (invM : Mt k r → Mt k r) := by
  have h : (invM : Mt k r → Mt k r) = fun x i j =>
      ((Matrix.of x : Mat k r).det)⁻¹ * (Matrix.of x : Mat k r).adjugate i j := by
    funext x i j
    simp only [invM, inv_eq, Matrix.smul_apply, smul_eq_mul]
  rw [h]
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact hof.matrix_det.measurable.inv.mul ((hof.matrix_adjugate).matrix_elem i j).measurable
end Formalism.FourierDecayAlt.P.B2x2
