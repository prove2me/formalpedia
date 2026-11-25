-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.Fk_enorm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:59.735101+00:00
-- url     : https://prove2.me/submissions/07beed0d-47cd-43ed-81a8-6bf9f5ae0cd7

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
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) :
    ‖Fk σ w W z z' q‖ₑ ≤ ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ := by
  unfold Fk
  rw [hWeq q hq z', hσ.2.1 q z', ContinuousLinearMap.mul_apply]
  have hn : ‖τ q (W z')‖ = ‖W z'‖ := by
    have h := hτu q hq (W z') (W z')
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖τ q (W z')‖ ^ 2 = ‖W z'‖ ^ 2 := by exact_mod_cast h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'
  have hA : ‖⟪τ q (W z'), W z⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖ :=
    (norm_inner_le_norm _ _).trans (by rw [hn, mul_comm])
  have hAe : ‖⟪τ q (W z'), W z⟫_ℂ‖ₑ ≤ ‖W z‖ₑ * ‖W z'‖ₑ := by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hA
  rw [enorm_mul]
  calc ‖⟪τ q (W z'), W z⟫_ℂ‖ₑ * ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ
      ≤ (‖W z‖ₑ * ‖W z'‖ₑ) * ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ := by gcongr
    _ = ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ := by ring
end Formalism.L2.S.Pv.EnergyAbs
