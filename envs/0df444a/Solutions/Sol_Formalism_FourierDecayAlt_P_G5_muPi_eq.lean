-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.muPi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:49:01.100446+00:00
-- url     : https://prove2.me/submissions/7a156edb-ff5c-44cc-ba6e-c8b0f854d362

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution (β : ℂ) (ι : Type) [Fintype ι] :
    muPi β ι = (Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  unfold muPi
  refine Measure.pi_eq fun s hs => ?_
  simp only [mu, Measure.smul_apply, volume_pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]
end Formalism.FourierDecayAlt.P.G5
