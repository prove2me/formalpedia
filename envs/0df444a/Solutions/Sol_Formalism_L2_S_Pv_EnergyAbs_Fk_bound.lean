-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.Fk_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:50.644273+00:00
-- url     : https://prove2.me/submissions/6a0d6473-1dd8-4b69-8ef8-ad911cf3029d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_fol_rep_norm
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_W_norm_trans

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
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) : ‖Fk σ w W z z' q‖ ≤ ‖W z‖ * ‖W z'‖ := by
  have h1 : ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖ := by
    calc ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W (q * z')‖ * ‖W z‖ := norm_inner_le_norm _ _
      _ = ‖W z‖ * ‖W z'‖ := by rw [W_norm_trans hWeq hτu hq z', mul_comm]
  have h2 : ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ 1 := by
    calc ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖σ z w‖ * ‖σ (q * z') w‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [(fol_rep_norm hσ), (fol_rep_norm hσ), hw, mul_one]
  show ‖⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖
  rw [norm_mul]
  calc ‖⟪W (q * z'), W z⟫_ℂ‖ * ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ (‖W z‖ * ‖W z'‖) * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖W z‖ * ‖W z'‖ := mul_one _
end Formalism.L2.S.Pv.EnergyAbs
