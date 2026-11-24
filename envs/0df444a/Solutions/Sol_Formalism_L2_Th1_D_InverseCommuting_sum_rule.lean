-- Prove2me | solution 1 for Formalism.L2.Th1.D.InverseCommuting.sum_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:26:47.813783+00:00
-- url     : https://prove2.me/submissions/06772881-4a9a-4ce5-a6f4-32a3eb6d796c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sim_refl
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sim_symm
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sim_trans
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_sim_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D.InverseCommuting
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {τ : Type}
namespace Formalism.L2.Th1.D.InverseCommuting
theorem _root_.solution {P : MvPowerSeries τ K → Prop} (h0 : P 0) (hadd : ∀ g g', P g → P g' → P (g + g'))
    (φ : MvPowerSeries τ K → MvPowerSeries τ K)
    (hφ : ∀ g g', P g → P g' → Simeq (φ (g + g')) (φ g + φ g'))
    {α : Type} (s : Finset α) (g : α → MvPowerSeries τ K) (hg : ∀ i ∈ s, P (g i)) :
    P (∑ i ∈ s, g i) ∧ Simeq (φ (∑ i ∈ s, g i)) (∑ i ∈ s, φ (g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using h0, ?_⟩
    have h := hφ 0 0 h0 h0
    rw [add_zero] at h
    have h' : Simeq (0 : MvPowerSeries τ K) (φ 0) := by
      unfold Simeq at h ⊢
      have e : (0 : MvPowerSeries τ K) - φ 0 = φ 0 - (φ 0 + φ 0) := by ring
      rw [e]
      exact h
    simpa using sim_symm h'
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hga := hg a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨hadd _ _ hga ih1, sim_trans (hφ _ _ hga ih1) (sim_add (sim_refl _) ih2)⟩
end Formalism.L2.Th1.D.InverseCommuting
