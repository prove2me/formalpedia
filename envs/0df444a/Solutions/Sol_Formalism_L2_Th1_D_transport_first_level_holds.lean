-- Prove2me | solution 1 for Formalism.L2.Th1.D.transport_first_level_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:31:04.40967+00:00
-- url     : https://prove2.me/submissions/aed171db-13da-48ce-affe-ecf5f07048d4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_cob_add
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_diffOne_add
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_swap_variables_add
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_cc_ps_gen
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_cob_hom
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_coboundary_commutes_homomorphism
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_swap_commutes_subst_log
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_divAB_cob
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_cc_of_cob
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_integral_subst_single_variable
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_sim_subst0
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_simeq_add_zero
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_sim_cob
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_simeq_coboundary_of_simeq_zero
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_sim_swap2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_cob_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_diffOne_add


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
open TraceNormBounds
namespace Formalism.L2.Th1.D
theorem _root_.solution : CoboundaryCocycleTransportAlongHom := by
  unfold CoboundaryCocycleTransportAlongHom
  intro K _ _ _ l hl hnl F hF FE θ phE ph hFE0 hθI hH hF1E hsim
  obtain ⟨hF0, hFI, hFc⟩ := hF
  obtain ⟨hdivE, hdE, hdsE⟩ := hF1E
  have hθ : PowerSeries.constantCoeff θ = 0 := hH.1
  have hccE : constantCoeff (cob FE phE) = 0 := by
    have h0 := hdivE 0 (Or.inl (by simp))
    first
    | exact h0
    | rwa [coeff_zero_eq_constantCoeff_apply] at h0
    | simpa using h0
  have hphE : PowerSeries.constantCoeff phE = 0 := cc_of_cob hFE0 hccE
  have hph : PowerSeries.constantCoeff ph = 0 := by
    have h1 := hsim.1
    rw [map_sub, cc_ps_gen (τ := Unit) hθ phE, hphE, sub_zero] at h1
    exact h1
  have hlam0 : Simeq ((ph - PowerSeries.subst θ phE : PowerSeries K) : MvPowerSeries Unit K) 0 := by
    unfold Simeq at hsim ⊢
    rw [sub_zero]
    exact hsim
  have hX3 : ∀ i : Fin 3, constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := fun i => by simp
  have hat3 : ∀ i : Fin 3, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX3 i) θ hθ
  have h03 : ∀ i, constantCoeff
      (![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] i) = 0 := by
    intro i
    fin_cases i
    · exact hat3 0
    · exact hat3 1
    · exact hat3 2
  have hI3 : ∀ i, Integral (![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] i) := by
    intro i
    fin_cases i
    · exact integral_subst_single_variable (0 : Fin 3) hθI
    · exact integral_subst_single_variable (1 : Fin 3) hθI
    · exact integral_subst_single_variable (2 : Fin 3) hθI
  have split : cob F ph = cob F (PowerSeries.subst θ phE) + cob F (ph - PowerSeries.subst θ phE) := by
    rw [← cob_add hF0]
    congr 1
    ring
  have hA : Simeq (d1 F (cob F (PowerSeries.subst θ phE))) 0 := by
    rw [cob_hom hF0 hFE0 hH phE, coboundary_commutes_homomorphism hF0 hFE0 hH]
    exact sim_subst0 h03 hI3 hdE
  have hB : Simeq (d1 F (cob F (ph - PowerSeries.subst θ phE))) 0 :=
    simeq_coboundary_of_simeq_zero hF0 hFI (sim_cob hF0 hFI hlam0)
  have hA' : Simeq (d1 F (swap2 (cob F (PowerSeries.subst θ phE)))) 0 := by
    rw [cob_hom hF0 hFE0 hH phE, swap_commutes_subst_log hθ, coboundary_commutes_homomorphism hF0 hFE0 hH]
    exact sim_subst0 h03 hI3 hdsE
  have hB' : Simeq (d1 F (swap2 (cob F (ph - PowerSeries.subst θ phE)))) 0 :=
    simeq_coboundary_of_simeq_zero hF0 hFI (sim_swap2 (sim_cob hF0 hFI hlam0))
  refine ⟨divAB_cob hl.two_le hF0 hFc hph, ?_, ?_⟩
  · rw [split, diffOne_add hF0]
    exact simeq_add_zero hA hB
  · rw [split, swap_variables_add, diffOne_add hF0]
    exact simeq_add_zero hA' hB'
end Formalism.L2.Th1.D
