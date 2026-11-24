-- Prove2me | solution 1 for Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf.exists_bruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:00:09.12624+00:00
-- url     : https://prove2.me/submissions/ed39aefe-7e2c-4ec9-bbf1-30f325184e5b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_QuotIndepStmt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_QuotIndepPf
import Theorems.Thm_Formalism_L2_SG_Pf_Weil_QuotInt_exists_fib_eq_one


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
theorem _root_.solution (S : Subgroup G) (hS : IsClosed (S : Set G)) (μS : Measure S)
    [μS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS] [IsOpenPosMeasure μS] [SFinite μS] :
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ x : G, ∫⁻ s, b ((s : G) * x) ∂μS = 1 := by
  have : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨β, hβm, hβ1⟩ := Formalism.L2.SG.Pf.Weil.QuotInt.exists_fib_eq_one hS μS.inv
  refine ⟨fun z => β z⁻¹, hβm.comp measurable_inv, fun x => ?_⟩
  have h := hβ1 x⁻¹
  unfold Formalism.L2.SG.Pf.Weil.QuotInt.fib at h
  rw [Measure.inv, lintegral_map (f := fun s : S => β (x⁻¹ * s)) (hβm.comp
    ((measurable_const_mul _).comp measurable_subtype_coe)) measurable_inv] at h
  simpa [mul_inv_rev] using h
end Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf
