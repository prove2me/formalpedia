-- Prove2me | solution 1 for FourierJacobi.Analysis.coreScaleExponent_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:44.864886+00:00
-- url     : https://prove2.me/submissions/e408d125-1c1e-4c3c-bd5c-37e050ca045c

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Theorems.Thm_FourierJacobi_Valuations_kernel_localFieldValuation_measurable
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top


set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_d9a05d5624_103
namespace FourierJacobi.Analysis
theorem _root_.solution : Measurable (coreScaleExponent K) := by
  have ha : Measurable (fun a : Kˣ => (a : K)) := MeasurableSpace.le_map_comap
  have hm := (kernel_localFieldValuation_measurable K).comp ha
  have he : coreScaleExponent K = (fun a : Kˣ =>
      (localFieldValuation K (a : K)).untopA) := by
    funext a
    exact (WithTop.untopA_eq_untop
      ((localFieldValuation_ne_top K (a : K)).mpr (Units.ne_zero a))).symm
  rw [he]
  exact hm.untopA
end FourierJacobi.Analysis
