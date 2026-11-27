-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.slice_integrable_finite_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:25.936973+00:00
-- url     : https://prove2.me/submissions/65289e68-2a71-4df6-80e6-5bf2d90c185b

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_thr_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_ae_Sn
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_norm_psiN
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_continuous_psiN
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_hS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sliceR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_integrand_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sizes1
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_slice_weight_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_integrable_slice_weight
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_hS_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_hS_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_exch_dLR
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_int_ck
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
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {A : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hT : TransportedAlt k r A m) (hF : B.InCC A m F) {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    (∀ μ ∈ B.GV k 0, Integrable (fun nn : Mt k r × Mt k r =>
        F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)) (D.μN.prod D.μN)) ∧
    B.InCC (k := k) (r := 0) (Ap r A m) m (sliceR D F c) := by
  obtain ⟨cF, hcF⟩ := hF
  obtain ⟨hAp, hAB, -, -⟩ := thr_facts hT
  obtain ⟨C, hC, hs⟩ := sizes1 k r {c} isCompact_singleton
    (by intro c' hc'; rw [Set.mem_singleton_iff.1 hc']; exact hc)
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  set M := max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m) with hMdef
  have hM : 0 ≤ M := by
    have : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg this m))
      (Real.rpow_nonneg (le_trans zero_le_one hC) _)
  have hβ : Integrable (beta0 (k := k) (r := r) M (Ap r A m)) (D.μN.prod D.μN) := integrable_slice_weight D.haarN M hAB
  have hbd := integrand_bound hT hcF hC hs (Set.mem_singleton c) hc
  have hg1 : ∀ μ ∈ B.GV k 0, B.gN μ ^ (-Ap r A m) ≤ 1 := fun μ hμ =>
    Real.rpow_le_one_of_one_le_of_nonpos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hμ) (by linarith)
  have hbd' : ∀ u v : List (B.Mat k 0), (∀ X ∈ u, B.unitLie k 0 X) → (∀ X ∈ v, B.unitLie k 0 X) →
      u.length + v.length ≤ m → ∀ g ∈ B.GV k 0, ∀ ξ, ‖B.dLR u v (hS F c ξ) g‖ ≤ beta0 M (Ap r A m) ξ := by
    intro u v hu hv hl g hg ξ
    refine (hbd u v hu hv hl g hg ξ).trans ?_
    calc beta0 M (Ap r A m) ξ * B.gN g ^ (-Ap r A m) ≤ beta0 M (Ap r A m) ξ * 1 :=
          mul_le_mul_of_nonneg_left (hg1 g hg) (slice_weight_nonneg hM ξ)
      _ = beta0 M (Ap r A m) ξ := mul_one _
  have hψ := norm_psiN D
  have hψm := (continuous_psiN D).aestronglyMeasurable (μ := D.μN.prod D.μN)
  have hh := hS_ck hcF.1 hc
  have hm : ∀ g ∈ B.GV k 0, AEStronglyMeasurable (fun ξ => hS F c ξ g) (D.μN.prod D.μN) :=
    fun g hg => hS_meas hcF.1 hc _ hg
  refine ⟨?_, ?_⟩
  · intro μ hμ
    have hI : Integrable (fun ξ => hS F c ξ μ) (D.μN.prod D.μN) := by
      refine Integrable.mono' hβ (hm μ hμ) (Eventually.of_forall fun ξ => ?_)
      have := hbd' [] [] (by simp) (by simp) (by simp) μ hμ ξ
      simpa [B.dLR, B.Rw] using this
    refine hI.congr ?_
    filter_upwards [ae_Sn D.haarN] with ξ hξ
    rw [hS_mem hξ]
    rfl
  · have hck := Formalism.FourierDecayAlt.P.Ux10.int_ck (psiN D) hψ hψm (hS F c) m hh hm _ hβ hbd'
    have hex := Formalism.FourierDecayAlt.P.Ux10.exch_dLR (psiN D) hψ hψm (hS F c) m hh hm _ hβ hbd'
    refine ⟨∫ ξ, beta0 M (Ap r A m) ξ ∂(D.μN.prod D.μN), ?_, ?_⟩
    · rw [sliceR_eq]; exact hck
    · intro u v hu hv hl g hg
      rw [sliceR_eq, hex u v hu hv hl g hg]
      have hgp : 0 < B.gN g := lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
      have hint : Integrable (fun ξ => beta0 M (Ap r A m) ξ * B.gN g ^ (-Ap r A m)) (D.μN.prod D.μN) :=
        hβ.mul_const _
      have hn : ‖∫ ξ, psiN D ξ • B.dLR u v (hS F c ξ) g ∂(D.μN.prod D.μN)‖ ≤
          ∫ ξ, beta0 M (Ap r A m) ξ * B.gN g ^ (-Ap r A m) ∂(D.μN.prod D.μN) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall fun ξ => by
          rw [norm_smul (psiN D ξ) (B.dLR u v (hS F c ξ) g)]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)).trans (hbd u v hu hv hl g hg ξ))
      rw [integral_mul_const] at hn
      have hpow : B.gN g ^ (Ap r A m) * B.gN g ^ (-Ap r A m) = 1 := by
        rw [Real.rpow_neg hgp.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hgp _).ne']
      calc B.gN g ^ (Ap r A m) * ‖∫ ξ, psiN D ξ • B.dLR u v (hS F c ξ) g ∂(D.μN.prod D.μN)‖
          ≤ B.gN g ^ (Ap r A m) * ((∫ ξ, beta0 M (Ap r A m) ξ ∂(D.μN.prod D.μN)) * B.gN g ^ (-Ap r A m)) :=
            mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hgp.le _)
        _ = ∫ ξ, beta0 M (Ap r A m) ξ ∂(D.μN.prod D.μN) := by
            rw [mul_comm, mul_assoc, mul_comm (B.gN g ^ (-Ap r A m)), hpow, mul_one]
end Formalism.FourierDecayAlt.P.SliceLastLevel
