-- Prove2me | solution 1 for Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf.lintegral_eq_bruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:31.521185+00:00
-- url     : https://prove2.me/submissions/b91cbe8b-1897-4df3-b32c-c8e49b7267fd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_QuotIndepStmt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_QuotIndepPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.QuotIndep
open Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf
theorem _root_.solution (S : Subgroup G) (μS : Measure S) (μ ν : Measure G) (b : G → ℝ≥0∞)
    (hbm : Measurable b) (hb1 : ∀ x : G, ∫⁻ s, b ((s : G) * x) ∂μS = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f ((s : G) * x) ∂μS ∂ν)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ (s : S) (x : G), f ((s : G) * x) = f x) :
    ∫⁻ x, f x ∂ν = ∫⁻ x, b x * f x ∂μ := by
  have h := hν (fun x => b x * f x) (hbm.mul hf)
  rw [h]
  refine lintegral_congr fun x => ?_
  simp_rw [hinv]
  rw [lintegral_mul_const (f x) (show Measurable fun s : S => b ((s : G) * x) from
    hbm.comp (measurable_subtype_coe.mul_const x)), hb1, one_mul]
end Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf
