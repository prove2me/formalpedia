-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.continuous_kG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:13:23.905827+00:00
-- url     : https://prove2.me/submissions/e73c78d0-676d-42b4-8ff0-d7256d580fa4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_continuous_rk1A

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (d : ℝ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) : Continuous (kG σ d w W W' γ) := by
  obtain ⟨-, -, -, hc⟩ := hσ
  have h1 : Continuous fun q : G × G => σ q.1 w := (hc w).comp continuous_fst
  have h2 : Continuous fun q : G × G => σ γ (σ q.2 w) :=
    (σ γ).continuous.comp ((hc w).comp continuous_snd)
  exact (continuous_const.mul (Continuous.inner (𝕜 := ℂ) h1 h2)).smul
    (continuous_rk1A (hW.comp continuous_fst) (hW'.comp continuous_snd))
end Formalism.L2.S.Pv.EnergyAbs
