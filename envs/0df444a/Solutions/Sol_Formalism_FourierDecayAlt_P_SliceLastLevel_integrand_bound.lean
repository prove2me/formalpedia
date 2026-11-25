-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.integrand_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:53.485698+00:00
-- url     : https://prove2.me/submissions/d2156b9d-3332-41f7-9e3d-3140dd2a6792

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_dLR_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_thr_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_nset_gv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_word_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_hS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_hS_not
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_letter_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dLR_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_dLR_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
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
theorem _root_.solution {A : ℝ} {m : ℕ} (hT : TransportedAlt k r A m) {F : B.Mat k r → (Wq →L[ℂ] Wp)} {cF : ℝ}
    (hF : B.CCle A m F cF) {K : Set (Fin r → ℂ)} {C : ℝ} (hC : 1 ≤ C)
    (hs : ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1))
    {c : Fin r → ℂ} (hcK : c ∈ K) (hc : ∀ a, c a ≠ 0)
    (u v : List (B.Mat k 0)) (hu : ∀ X ∈ u, B.unitLie k 0 X) (hv : ∀ X ∈ v, B.unitLie k 0 X)
    (hl : u.length + v.length ≤ m) (μ : B.Mat k 0) (hμ : μ ∈ B.GV k 0) (ξ : Mt k r × Mt k r) :
    ‖B.dLR u v (hS F c ξ) μ‖ ≤
      (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) *
        (B.gN (Matrix.of ξ.1 : B.Mat k r) ^ (-Ap r A m) * B.gN (Matrix.of ξ.2 : B.Mat k r) ^ (-Ap r A m)) *
        B.gN μ ^ (-Ap r A m) := by
  obtain ⟨hAp, -, -, -⟩ := thr_facts hT
  have hκ : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + k + 1 := by omega
    exact_mod_cast this
  by_cases hξ : ξ ∈ Sn k r
  · rw [hS_mem hξ]
    set n : B.Mat k r := Matrix.of ξ.1
    set n' : B.Mat k r := Matrix.of ξ.2
    have hn : n ∈ Nset k r := hξ.1
    have hn' : n' ∈ Nset k r := hξ.2
    rw [dLR_phi c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (nset_gv hn)) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (nset_gv hn')) F u v]
    obtain ⟨h1, h2, h3⟩ := hs c hcK n hn n' hn' μ hμ
    have hw := word_bound hT hF hC hκ hc hn hn' hμ h1 h2 h3
      (u.map fun Y => n⁻¹ * emb0 k r Y * n) (v.map fun Y => n'⁻¹ * emb0 k r Y * n')
      (by
        intro X hX
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact letter_bound hn (hu Y hY))
      (by
        intro X hX
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact letter_bound hn' (hv Y hY))
      (by simpa using hl)
    refine hw.trans (le_of_eq ?_)
    have hn0 : 0 ≤ B.gN n := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn))
    have hn0' : 0 ≤ B.gN n' := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn'))
    have hμ0 : 0 ≤ B.gN μ := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hμ)
    rw [Real.mul_rpow (mul_nonneg hn0 hn0') hμ0, Real.mul_rpow hn0 hn0']
    ring
  · rw [hS_not hξ, Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_zero]
    simp only [Pi.zero_apply, norm_zero]
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    have h0 : 0 ≤ max cF 0 := le_max_right _ _
    have hg : ∀ M : B.Mat k r, 0 ≤ B.gN M ^ (-Ap r A m) := fun M => Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hg0 : 0 ≤ B.gN μ ^ (-Ap r A m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hC3 : 0 ≤ C ^ (3 * Ap r A m) := Real.rpow_nonneg hC0 _
    have hk : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg hk m)) hC3)
      (mul_nonneg (hg _) (hg _))) hg0
end Formalism.FourierDecayAlt.P.SliceLastLevel
