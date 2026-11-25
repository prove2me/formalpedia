-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.kF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:12:05.241193+00:00
-- url     : https://prove2.me/submissions/4a4bd7c1-41d0-4147-aa05-cbbf4ceec3c0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_fol_rep_mul
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_W_inner_trans

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
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hSinv : ∀ a ∈ S, a⁻¹ ∈ S)
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {s t : G} (hs : s ∈ S) :
    ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ * ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = Fk σ w W z z' (s * t⁻¹) := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  have e1 : ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ = ⟪W (s * t⁻¹ * z'), W z⟫_ℂ := by
    rw [← W_inner_trans hWeq hτu hs (t⁻¹ * z') (s⁻¹ * z), mul_assoc, mul_inv_cancel_left]
  have e2 : ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = ⟪σ z w, σ (s * t⁻¹ * z') w⟫_ℂ := by
    rw [← hin s (σ (s⁻¹ * z) w) (σ (t⁻¹ * z') w), ← (fol_rep_mul hσ), ← (fol_rep_mul hσ), mul_inv_cancel_left,
      mul_assoc]
  rw [e1, e2]
  rfl
end Formalism.L2.S.Pv.EnergyAbs
