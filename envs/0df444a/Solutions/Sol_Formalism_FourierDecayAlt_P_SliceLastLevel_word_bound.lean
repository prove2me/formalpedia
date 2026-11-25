-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.word_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:53.973859+00:00
-- url     : https://prove2.me/submissions/df212528-eb17-4ed3-8c1d-a02883a31daf

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_phi_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_thr_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_nset_gv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_pow_trade
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SliceLastLevel_allLie_lr__eac81ef3b4e2
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_bound_scaled
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_lrt_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_le_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_nonneg
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {A : ℝ} {m : ℕ} (hT : TransportedAlt k r A m) {F : B.Mat k r → E} {cF : ℝ} (hF : B.CCle A m F cF)
    {C κ : ℝ} (hC : 1 ≤ C) (hκ : 1 ≤ κ) {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {μ : B.Mat k 0} (hμ : μ ∈ B.GV k 0)
    (hs1 : B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r))
    (hs2 : B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r))
    (hs3 : B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1))
    (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.inLie k r X ∧ ‖X‖ ≤ κ * B.gN n ^ 2)
    (hv : ∀ X ∈ v, B.inLie k r X ∧ ‖X‖ ≤ κ * B.gN n' ^ 2) (hl : u.length + v.length ≤ m) :
    ‖B.dLR u v F (phi k r c n n' μ)‖ ≤
      max cF 0 * (κ * C ^ 2) ^ m *
        (C ^ (3 * Ap r A m) * ((B.gN n * B.gN n') * B.gN μ) ^ (-Ap r A m)) := by
  obtain ⟨hAp, -, hA6, hle⟩ := thr_facts hT
  set g := phi k r c n n' μ with hgdef
  have hg : g ∈ B.GV k r := phi_mem hc (nset_gv hn) (nset_gv hn') hμ
  set G := B.gN g with hGdef
  have hG : 1 ≤ G := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hG0 : 0 < G := lt_of_lt_of_le one_pos hG
  have hn1 : 1 ≤ B.gN n := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn)
  have hn1' : 1 ≤ B.gN n' := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn')
  have hμ1 : 1 ≤ B.gN μ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hμ
  have hb := Formalism.FourierDecayAlt.P.B4.bound_scaled hF (Formalism.FourierDecayAlt.P.B4.lr u v) (Formalism.FourierDecayAlt.P.B4.lrt_lr u v)
    (allLie_lr' (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1))
    (by rw [Formalism.FourierDecayAlt.P.B4.length_lr]; exact hl) g hg
  rw [← Formalism.FourierDecayAlt.P.B4.dLR_eq] at hb
  set K : ℝ := κ * C ^ 2 * G ^ (4 * r) with hK
  have hK1 : 1 ≤ K := by
    have : 1 ≤ C ^ 2 := one_le_pow₀ hC
    have : 1 ≤ G ^ (4 * r) := one_le_pow₀ hG
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ κ * C ^ 2 * G ^ (4 * r) := by gcongr
  have hsq : ∀ x : ℝ, 0 ≤ x → x ≤ C * G ^ (2 * r) → κ * x ^ 2 ≤ K := by
    intro x hx0 hx
    have : x ^ 2 ≤ (C * G ^ (2 * r)) ^ 2 := pow_le_pow_left₀ hx0 hx 2
    calc κ * x ^ 2 ≤ κ * (C * G ^ (2 * r)) ^ 2 := by gcongr
      _ = K := by rw [hK]; ring
  have hpn : Formalism.FourierDecayAlt.P.B4.pn (Formalism.FourierDecayAlt.P.B4.lr u v) ≤ K ^ m := by
    refine (Formalism.FourierDecayAlt.P.B4.pn_le_pow _ K ?_).trans ?_
    · intro x hx
      simp only [Formalism.FourierDecayAlt.P.B4.lr, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).2.trans (hsq _ (by positivity) hs1)
      · exact (hv X hX).2.trans (hsq _ (by positivity) hs2)
    · rw [Formalism.FourierDecayAlt.P.B4.length_lr]; exact pow_le_pow_right₀ hK1 hl
  have hcF : 0 ≤ max cF 0 := le_max_right _ _
  have h1 : G ^ A * ‖B.dLR u v F g‖ ≤ K ^ m * max cF 0 := by
    refine hb.trans ?_
    calc Formalism.FourierDecayAlt.P.B4.pn (Formalism.FourierDecayAlt.P.B4.lr u v) * cF ≤ Formalism.FourierDecayAlt.P.B4.pn (Formalism.FourierDecayAlt.P.B4.lr u v) * max cF 0 := by
          gcongr
          · exact Formalism.FourierDecayAlt.P.B4.pn_nonneg _
          · exact le_max_left _ _
      _ ≤ K ^ m * max cF 0 := by gcongr
  have hGA : 0 < G ^ A := Real.rpow_pos_of_pos hG0 A
  have h2 : ‖B.dLR u v F g‖ ≤ K ^ m * max cF 0 * G ^ (-A) := by
    rw [Real.rpow_neg hG0.le, ← div_eq_mul_inv, le_div_iff₀ hGA, mul_comm]
    exact h1

  have h3 : K ^ m * G ^ (-A) = (κ * C ^ 2) ^ m * G ^ (-(A - 4 * (r : ℝ) * m)) := by
    rw [hK, mul_pow, ← pow_mul, mul_assoc]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_add hG0]
    congr 1
    push_cast; ring

  have hP0 : 0 < (B.gN n * B.gN n') * B.gN μ := by positivity
  have hPb : (B.gN n * B.gN n') * B.gN μ ≤ C ^ (3 : ℝ) * G ^ (5 * (r : ℝ) + 1) := by
    have e1 : C ^ (3 : ℝ) * G ^ (5 * (r : ℝ) + 1) = (C * G ^ (2 * r)) * (C * G ^ (2 * r)) * (C * G ^ (r + 1)) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        show (5 * (r : ℝ) + 1) = ((5 * r + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [show 5 * r + 1 = 2 * r + 2 * r + (r + 1) by ring, pow_add, pow_add]; ring
    rw [e1]
    gcongr
  have h4 := pow_trade (b := A - 4 * (r : ℝ) * m) hG hP0 hC hAp.le (by positivity) hPb (by
    have : (0 : ℝ) ≤ 2 * (r : ℝ) * m := by positivity
    linarith)
  calc ‖B.dLR u v F g‖ ≤ K ^ m * max cF 0 * G ^ (-A) := h2
    _ = max cF 0 * (K ^ m * G ^ (-A)) := by ring
    _ = max cF 0 * ((κ * C ^ 2) ^ m * G ^ (-(A - 4 * (r : ℝ) * m))) := by rw [h3]
    _ ≤ max cF 0 * ((κ * C ^ 2) ^ m * (C ^ (3 * Ap r A m) * ((B.gN n * B.gN n') * B.gN μ) ^ (-Ap r A m))) := by
        gcongr
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.SliceLastLevel
