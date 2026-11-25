-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.Gw_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:46.745328+00:00
-- url     : https://prove2.me/submissions/7b03b00f-12c3-4093-8b64-7dcfaf934439

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_nset_gv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_word_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_adR_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_adR_norm
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
open scoped ContDiff
set_option linter.style.haveILetI false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r d : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {A : ℝ} {m : ℕ} (hT : TransportedAlt k r A m) {F : B.Mat k r → (Wq →L[ℂ] Wp)} {cF : ℝ}
    (hF : B.CCle A m F cF) {K : Set (Fin r → ℂ)} {C : ℝ} (hC : 1 ≤ C)
    (hs : ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1))
    {c : Fin r → ℂ} (hcK : c ∈ K) (hc : ∀ a, c a ≠ 0) {ξ : Mt k r × Mt k r} (hξ : ξ ∈ Sn k r)
    {μ : B.Mat k 0} (hμ : μ ∈ B.GV k 0) (w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)) (hw : w.length ≤ m) :
    ‖Gw F ξ w (phi k r c (Matrix.of ξ.1) (Matrix.of ξ.2) μ)‖ ≤
      beta0 (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) (Ap r A m) ξ := by
  obtain ⟨hAp, -, -, -⟩ := thr_facts hT
  have hκ : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + k + 1 := by omega
    exact_mod_cast this
  set n : B.Mat k r := Matrix.of ξ.1
  set n' : B.Mat k r := Matrix.of ξ.2
  have hn : n ∈ Nset k r := hξ.1
  have hn' : n' ∈ Nset k r := hξ.2
  obtain ⟨h1, h2, h3⟩ := hs c hcK n hn n' hn' μ hμ
  have hw' := word_bound hT hF hC hκ hc hn hn' hμ h1 h2 h3 [] (w.map (adR n')) (by simp)
    (by
      intro X hX
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hX
      exact ⟨adR_lie (nset_gv hn') i, adR_norm (nset_gv hn') i⟩)
    (by simpa using hw)
  have hn0 : 0 ≤ B.gN n := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn))
  have hn0' : 0 ≤ B.gN n' := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn'))
  have hμ1 : 1 ≤ B.gN μ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hμ
  have hμp : B.gN μ ^ (-Ap r A m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hμ1 (by linarith)
  have hM : 0 ≤ max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m) := by
    have : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg this m))
      (Real.rpow_nonneg (le_trans zero_le_one hC) _)
  have hb0 : 0 ≤ B.gN n ^ (-Ap r A m) * B.gN n' ^ (-Ap r A m) :=
    mul_nonneg (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg hn0' _)
  refine hw'.trans ?_
  rw [Real.mul_rpow (mul_nonneg hn0 hn0') (le_trans zero_le_one hμ1), Real.mul_rpow hn0 hn0']
  unfold beta0
  calc max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m *
        (C ^ (3 * Ap r A m) * (B.gN n ^ (-Ap r A m) * B.gN n' ^ (-Ap r A m) * B.gN μ ^ (-Ap r A m)))
      = (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) *
          (B.gN n ^ (-Ap r A m) * B.gN n' ^ (-Ap r A m)) * B.gN μ ^ (-Ap r A m) := by ring
    _ ≤ (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) *
          (B.gN n ^ (-Ap r A m) * B.gN n' ^ (-Ap r A m)) * 1 := by gcongr
    _ = _ := by rw [mul_one]
end Formalism.FourierDecayAlt.P.SliceLastLevel
