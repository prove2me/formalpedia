-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.Fk_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:54.806893+00:00
-- url     : https://prove2.me/submissions/eae49728-4a6f-4752-943e-5b4c8352847a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
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
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    {X : Type} [TopologicalSpace X] {a b c : X → G} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => Fk σ w W (a x) (b x) (c x)) := by
  obtain ⟨-, -, -, hσc⟩ := id hσ
  have hcb : Continuous fun x => c x * b x := hc.mul hb
  have h1 : Continuous fun x => W (c x * b x) := hWc.comp hcb
  have h2 : Continuous fun x => W (a x) := hWc.comp ha
  have h3 : Continuous fun x => σ (a x) w := (hσc w).comp ha
  have h4 : Continuous fun x => σ (c x * b x) w := (hσc w).comp hcb
  show Continuous fun x => ⟪W (c x * b x), W (a x)⟫_ℂ * ⟪σ (a x) w, σ (c x * b x) w⟫_ℂ
  exact (h1.inner h2).mul (h3.inner h4)
end Formalism.L2.S.Pv.EnergyAbs
