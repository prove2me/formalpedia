-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.coef_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:14:36.843432+00:00
-- url     : https://prove2.me/submissions/ce15a759-aa1b-45ba-b296-4595d763c695

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
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) (γ z u z' u' : G) :
    ⟪σ (u⁻¹ * z) w, σ γ (σ (u'⁻¹ * z') w)⟫_ℂ = ⟪σ z w, σ (u * γ * u'⁻¹) (σ z' w)⟫_ℂ := by
  obtain ⟨h1, hmul, hinn, -⟩ := hσ
  have e : ∀ a : HH, σ u (σ u⁻¹ a) = a := fun a => by
    rw [← ContinuousLinearMap.mul_apply, ← hmul, mul_inv_cancel, h1, ContinuousLinearMap.one_apply]
  rw [← hinn u, hmul u⁻¹ z, ContinuousLinearMap.mul_apply, e]
  simp only [hmul, ContinuousLinearMap.mul_apply]
end Formalism.L2.S.Pv.EnergyAbs
