-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.continuous_coef5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:40.837997+00:00
-- url     : https://prove2.me/submissions/7febcb06-026e-46ba-b4cb-54e61508a4ec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt

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
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) (γ : G) :
    Continuous (fun q : G × G × G × G => ⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹) (σ q.2.1 w)⟫_ℂ) := by
  obtain ⟨-, hmul, -, hc⟩ := hσ
  have e : (fun q : G × G × G × G => ⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹) (σ q.2.1 w)⟫_ℂ) =
      fun q => ⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹ * q.2.1) w⟫_ℂ := by
    funext q
    rw [hmul (q.2.2.1 * γ * q.2.2.2⁻¹) q.2.1, ContinuousLinearMap.mul_apply]
  rw [e]
  have hg : Continuous fun q : G × G × G × G => q.2.2.1 * γ * q.2.2.2⁻¹ * q.2.1 := by fun_prop
  exact ((hc w).comp continuous_fst).inner ((hc w).comp hg)
end Formalism.L2.S.Pv.EnergyAbs
