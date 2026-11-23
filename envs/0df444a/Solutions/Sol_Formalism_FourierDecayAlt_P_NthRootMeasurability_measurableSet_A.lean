-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NthRootMeasurability.measurableSet_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:07.81197+00:00
-- url     : https://prove2.me/submissions/6868d967-20fa-4f5c-b5a3-f90bc9a4cc55

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_measurable_R

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NthRootMeasurability
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.NthRootMeasurability
theorem _root_.solution (s k : ℕ) : MeasurableSet (A s k) := by
  have h1 : MeasurableSet {z : ℂ | z ≠ 0} := (measurableSet_singleton (0 : ℂ)).compl
  have h2 : MeasurableSet {z : ℂ | R s k (z ^ s) = z} :=
    measurableSet_eq_fun ((measurable_R s k).comp (by fun_prop)) measurable_id
  exact h1.inter h2
end Formalism.FourierDecayAlt.P.NthRootMeasurability
