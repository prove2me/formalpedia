-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.integral_norm_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:59.674857+00:00
-- url     : https://prove2.me/submissions/597d0563-01e1-4da3-b662-66ff6a58ffd7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {ν : Measure G} {W : G → V} (hWc : Continuous W) (h2 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν = 1) :
    ∫ z, ‖W z‖ ^ 2 ∂ν = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
    ((hWc.norm.pow 2).aestronglyMeasurable)]
  have h : (fun x => ENNReal.ofReal (‖W x‖ ^ 2)) = fun x => ‖W x‖ₑ ^ 2 := by
    funext x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [h, h2]
  simp
end Formalism.L2.S.Pv.EnergyAbs
