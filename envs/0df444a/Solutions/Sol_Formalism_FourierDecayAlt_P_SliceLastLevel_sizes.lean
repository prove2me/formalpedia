-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.sizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:45:26.700847+00:00
-- url     : https://prove2.me/submissions/fab8209a-bfd5-40f7-bce7-986ada4c250d

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_castW_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_phi_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_bc_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_contK
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_gN_le_of_EB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_entry_le_gN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution (k r : ℕ) (K : Set (Fin r → ℂ)) (hK : IsCompact K) (hK0 : ∀ c ∈ K, ∀ a, c a ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    refine ⟨((2 * 0 + k + 1 : ℕ) : ℝ), by positivity, fun c hc n hn n' hn' μ hμ => ?_⟩
    rw [sz_N_zero hn, sz_N_zero hn']
    have hb : phi k 0 c 1 1 μ = bigCell k 0 c (castW μ) := by simp [phi]
    have hG : 1 ≤ B.gN (phi k 0 c 1 1 μ) :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (sz_phi_mem c (hK0 c hc) (sz_N_one k 0) (sz_N_one k 0) hμ)
    have e1 : B.gN (1 : B.Mat k 0) ≤ ((2 * 0 + k + 1 : ℕ) : ℝ) * 1 :=
      gN_le_of_EB _ (fun i j => by rw [Matrix.one_apply]; split_ifs <;> simp) (by norm_num)
    refine ⟨by simpa using e1, by simpa using e1, ?_⟩
    have eμ : EB μ (B.gN (phi k 0 c 1 1 μ)) := fun i j => by
      rw [← sz_bc_zero c μ i j, ← hb]; exact entry_le_gN _ i j
    refine (gN_le_of_EB μ eμ (by linarith)).trans ?_
    rw [zero_add, pow_one]
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    obtain ⟨Bd, hBd⟩ := hK.exists_bound_of_continuousOn (sz_contK s K hK0)
    set Q : ℝ := |Bd| + 2 + ((s + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) with hQdef
    refine ⟨((2 * (s + 1) + k + 1 : ℕ) : ℝ) * Q ^ 5, by positivity, fun c hc n hn n' hn' μ hμ => ?_⟩
    have hc0 := hK0 c hc
    have hf := hBd c hc
    have hK1 : 0 ≤ unitriangularFactorConstant c := by unfold unitriangularFactorConstant; exact Finset.sum_nonneg fun i _ => by positivity
    have hsum : 0 ≤ ∑ a, ‖c a‖ := Finset.sum_nonneg fun a _ => norm_nonneg _
    have hd : 0 ≤ (s.factorial : ℝ) / ‖∏ a, c a‖ := by positivity
    have hfe : ‖2 * unitriangularFactorConstant c + ∑ a, ‖c a‖ + (s.factorial : ℝ) / ‖∏ a, c a‖‖ =
        2 * unitriangularFactorConstant c + ∑ a, ‖c a‖ + (s.factorial : ℝ) / ‖∏ a, c a‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hfe] at hf
    have hBdQ' : Bd ≤ Q := by
      rw [hQdef]
      have h1 := le_abs_self Bd
      have h2 : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hQ2 : 2 ≤ Q := by
      rw [hQdef]
      have h1 := abs_nonneg Bd
      have h2 : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hQr : ((s + 1 : ℕ) : ℝ) ≤ Q := by
      rw [hQdef]
      have h1 := abs_nonneg Bd
      have h3 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hQk : ((k + 1 : ℕ) : ℝ) ≤ Q := by
      rw [hQdef]
      have h1 := abs_nonneg Bd
      have h2 : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hQc : ∀ a, ‖c a‖ ≤ Q := fun a => by
      have := Finset.single_le_sum (f := fun a => ‖c a‖) (fun a _ => norm_nonneg _) (Finset.mem_univ a)
      linarith
    have hQK : 2 * unitriangularFactorConstant c ≤ Q := by linarith
    have hQd : (s.factorial : ℝ) / ‖∏ a, c a‖ ≤ Q := by linarith
    have hG : 1 ≤ B.gN (n⁻¹ * bigCell k (s + 1) c (castW μ) * n') :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (sz_phi_mem c hc0 hn hn' hμ)
    obtain ⟨e1, e2, e3⟩ := sz_core k s c hc0 Q hQ2 hQr hQk hQc hQK hQd hn hn' (castW μ) hG
    have hphi : phi k (s + 1) c n n' μ = n⁻¹ * bigCell k (s + 1) c (castW μ) * n' := rfl
    rw [hphi]
    set G := B.gN (n⁻¹ * bigCell k (s + 1) c (castW μ) * n')
    have hG0 : 0 ≤ G := by linarith
    have hQ0 : 0 ≤ Q := by linarith
    have hT : 0 ≤ Q ^ 5 * G ^ (2 * s + 2) := by positivity
    have e2r : 2 * (s + 1) = 2 * s + 2 := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [e2r]; refine (gN_le_of_EB n e1 hT).trans (le_of_eq ?_); ring
    · rw [e2r]; refine (gN_le_of_EB n' e2 hT).trans (le_of_eq ?_); ring
    · have eμ : EB μ (Q ^ 5 * G ^ (s + 2)) := fun i j => by rw [sz_castW_apply μ i j]; exact e3 _ _
      have hT' : 0 ≤ Q ^ 5 * G ^ (s + 2) := by positivity
      refine (gN_le_of_EB μ eμ hT').trans ?_
      rw [show s + 1 + 1 = s + 2 by ring, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 2 * 0 + k + 1 ≤ 2 * (s + 1) + k + 1)) hT'
end Formalism.FourierDecayAlt.P.SliceLastLevel
