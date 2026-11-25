-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.scalar_majorant_weak_threshold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:57.794661+00:00
-- url     : https://prove2.me/submissions/a77cc712-648d-4138-bbba-554403f80a6a

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalMeasurabilityWeakThreshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haarW
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_mul_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_sL_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_sR_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_ad_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_haar_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_list_prod_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_orbit3
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_real_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_uw_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_gN_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_NInt_lint_gN_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_gN_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_n_mem_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_weyl_subgroup_compact
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
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism.FourierDecayAlt.P.WeakDominationMajorants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
theorem _root_.solution : Formalism.FourierDecayAlt.P.WeakThresholdClauses.NNMajW := by
  intro k r Wp Wq _ _ _ _ D A m hThr K hK hKO
  obtain ⟨C3, hC3, horb⟩ := orbit3 D.z D.z' K hK hKO
  obtain ⟨cW, hcW, hW⟩ := uw_bound D.z D.z_mem D.T_pos
  obtain ⟨cW', hcW', hW'⟩ := uw_bound D.z' D.z'_mem D.T'_pos

  have hc : 1 ≤ max cW cW' := le_trans hcW (le_max_left _ _)
  have hC4 : 1 ≤ max 1 (C3 * max cW cW' ^ (6 * r)) := le_max_left _ _
  set c := max cW cW' with hc_def
  set C4 := max 1 (C3 * c ^ (6 * r)) with hC4_def
  set NN : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hNN
  have hNN1 : 1 ≤ NN := by rw [hNN]; exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  set Λ1 := max 1 (NN * c ^ 2 * C4 ^ 2) with hΛ1_def
  have hΛ1 : 1 ≤ Λ1 := le_max_left _ _
  set A1 := A - 6 * (r : ℝ) * (m : ℝ) with hA1_def

  have hA1pos : 0 < A1 := hThr.1
  set β := A1 / (6 * (r : ℝ) + 1) with hβ_def
  have hβ0 : 0 ≤ β := div_nonneg hA1pos.le (by positivity)
  have hβA : 6 * (r : ℝ) * β ≤ A1 := by
    rw [hβ_def, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hthr : r = 0 ∨ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) < β := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact Or.inl h
    · right
      rw [hβ_def, lt_div_iff₀ (by positivity)]
      exact hThr.2

  set f : Mt k r → ℝ := fun x => gN (Matrix.of x : Mat k r) ^ (-β) with hf_def
  refine ⟨fun p => Λ1 ^ m * (C4 ^ β) ^ 2 * (f p.1.2 * f p.2.2), ?_, ?_⟩
  ·
    have : SigmaFinite D.μN := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
    have : IsFiniteMeasure D.μW := haar_finite D.haarW (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos)
    have : IsFiniteMeasure D.μW' :=
      haar_finite D.haarW' (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos)
    have hfi : Integrable f D.μN := by
      refine ⟨((NInt.gN_cont k r).measurable.pow_const (-β)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (Orb.gN_nonneg _) _)]
      exact NInt.lint_gN_fin k r D.μN D.haarN β hthr
    have h1 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * f q.2) (D.μW.prod D.μN) :=
      (integrable_const (1 : ℝ)).mul_prod hfi
    have h2 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * f q.2) (D.μW'.prod D.μN) :=
      (integrable_const (1 : ℝ)).mul_prod hfi
    have h3 := (h1.mul_prod h2).const_mul (Λ1 ^ m * (C4 ^ β) ^ 2)
    refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [one_mul]
  · intro u v hu hv hl g hg
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp

    have hh : Matrix.of p.1.1 ∈ GV k r := hp.1.1
    have hn : Matrix.of p.1.2 ∈ Nset k r := hp.2.1
    have hh' : Matrix.of p.2.1 ∈ GV k r := hp.2.2.1.1
    have hn' : Matrix.of p.2.2 ∈ Nset k r := hp.2.2.2
    have hgG : g ∈ GV k r := (hKO hg).1
    have hx : sgs p g ∈ GV k r := by
      simp only [sgs]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
        (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hh) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (Orb.n_mem_G hn))) hgG) (Orb.n_mem_G hn')) hh'
    set X := gN (sgs p g) with hX_def
    have hX1 : 1 ≤ X := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx

    have hY : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 = Matrix.of p.1.1 * sgs p g * (Matrix.of p.2.1)⁻¹ := by
      have hs : sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
        simp only [sgs, Matrix.mul_assoc]
      rw [hs, Matrix.mul_assoc (Matrix.of p.1.1)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit hh),
        Matrix.mul_nonsing_inv_cancel_right _ _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit hh')]
    have hgh : gN (Matrix.of p.1.1) ≤ c := (hW _ hp.1).trans (le_max_left _ _)
    have hgh' : gN (Matrix.of p.2.1) ≤ c := (hW' _ hp.2.2.1).trans (le_max_right _ _)
    have hYb : gN ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) ≤ c ^ 2 * X := by
      rw [hY]
      have e1 := Formalism.FourierDecayAlt.P.B6.gN_mul_le (Matrix.of p.1.1 * sgs p g) (Matrix.of p.2.1)⁻¹
      have e2 := Formalism.FourierDecayAlt.P.B6.gN_mul_le (Matrix.of p.1.1) (sgs p g)
      rw [Orb.gN_inv hh'] at e1
      have := Orb.gN_nonneg (sgs p g); have := Orb.gN_nonneg (Matrix.of p.1.1)
      calc _ ≤ gN (Matrix.of p.1.1 * sgs p g) * gN (Matrix.of p.2.1) := e1
        _ ≤ (c * X) * c := by
            have e3 : gN (Matrix.of p.1.1 * sgs p g) ≤ c * X :=
              e2.trans (mul_le_mul_of_nonneg_right hgh (Orb.gN_nonneg _))
            exact mul_le_mul e3 hgh' (Orb.gN_nonneg _) (by positivity)
        _ = c ^ 2 * X := by ring
    have hYX : gN ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) ^ (3 * r) ≤ c ^ (6 * r) * X ^ (3 * r) := by
      calc _ ≤ (c ^ 2 * X) ^ (3 * r) := pow_le_pow_left₀ (Orb.gN_nonneg _) hYb _
        _ = c ^ (6 * r) * X ^ (3 * r) := by rw [mul_pow, ← pow_mul]; ring_nf
    obtain ⟨hb1, hb2⟩ := horb g hg _ hn _ hn'
    have hXr : 0 ≤ X ^ (3 * r) := by positivity
    have hG1 : gN (Matrix.of p.1.2) ≤ C4 * X ^ (3 * r) := by
      refine hb1.trans ?_
      calc C3 * _ ≤ C3 * (c ^ (6 * r) * X ^ (3 * r)) := mul_le_mul_of_nonneg_left hYX hC3
        _ = (C3 * c ^ (6 * r)) * X ^ (3 * r) := by ring
        _ ≤ C4 * X ^ (3 * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) hXr
    have hG2 : gN (Matrix.of p.2.2) ≤ C4 * X ^ (3 * r) := by
      refine hb2.trans ?_
      calc C3 * _ ≤ C3 * (c ^ (6 * r) * X ^ (3 * r)) := mul_le_mul_of_nonneg_left hYX hC3
        _ = (C3 * c ^ (6 * r)) * X ^ (3 * r) := by ring
        _ ≤ C4 * X ^ (3 * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) hXr

    have hlet : ∀ s h : Mat k r, s = Matrix.of p.1.2 * Matrix.of p.1.1 ∨ s = Matrix.of p.2.2 * Matrix.of p.2.1 →
        s ∈ GV k r → ∀ Y : Mat k r, unitLie k r Y → ‖s⁻¹ * Y * s‖ ≤ Λ1 * X ^ (6 * r) := by
      intro s _ hs hsG Y hYu
      have hsb : gN s ≤ C4 * X ^ (3 * r) * c := by
        rcases hs with rfl | rfl
        · exact (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul hG1 hgh (Orb.gN_nonneg _) (by positivity))
        · exact (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul hG2 hgh' (Orb.gN_nonneg _) (by positivity))
      refine (ad_bd hsG hYu).trans ?_
      calc NN * gN s ^ 2 ≤ NN * (C4 * X ^ (3 * r) * c) ^ 2 := by
            gcongr; exact Orb.gN_nonneg _
        _ = (NN * c ^ 2 * C4 ^ 2) * X ^ (6 * r) := by ring_nf
        _ ≤ Λ1 * X ^ (6 * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hΛX : 1 ≤ Λ1 * X ^ (6 * r) := one_le_mul_of_one_le_of_one_le hΛ1 (one_le_pow₀ hX1)
    have hPu : (u.map fun Y => ‖AdL p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ u.length := by
      have := list_prod_le (u.map fun Y => ‖AdL p Y‖) (Λ1 * X ^ (6 * r)) (by
        intro y hy
        obtain ⟨Y, hYu, rfl⟩ := List.mem_map.1 hy
        exact ⟨norm_nonneg _, hlet _ (Matrix.of p.1.1) (Or.inl rfl) (Formalism.FourierDecayAlt.P.JFxDs2.sL_mem hp) Y (hu Y hYu)⟩)
      simpa using this
    have hPv : (v.map fun Y => ‖AdR p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ v.length := by
      have := list_prod_le (v.map fun Y => ‖AdR p Y‖) (Λ1 * X ^ (6 * r)) (by
        intro y hy
        obtain ⟨Y, hYv, rfl⟩ := List.mem_map.1 hy
        exact ⟨norm_nonneg _, hlet _ (Matrix.of p.2.1) (Or.inr rfl) (Formalism.FourierDecayAlt.P.JFxDs2.sR_mem hp) Y (hv Y hYv)⟩)
      simpa using this
    have hP : (u.map fun Y => ‖AdL p Y‖).prod * (v.map fun Y => ‖AdR p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ m := by
      have hu0 : 0 ≤ (u.map fun Y => ‖AdL p Y‖).prod := List.prod_nonneg fun y hy => by
        obtain ⟨Y, _, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _
      calc _ ≤ (Λ1 * X ^ (6 * r)) ^ u.length * (Λ1 * X ^ (6 * r)) ^ v.length :=
            mul_le_mul hPu hPv (List.prod_nonneg fun y hy => by
              obtain ⟨Y, _, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _) (by positivity)
        _ = (Λ1 * X ^ (6 * r)) ^ (u.length + v.length) := by rw [pow_add]
        _ ≤ (Λ1 * X ^ (6 * r)) ^ m := pow_le_pow_right₀ hΛX hl
    exact real_step X (gN (Matrix.of p.1.2)) (gN (Matrix.of p.2.2)) C4 Λ1 A A1 β _ m r hX1 hC4
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (Orb.n_mem_G hn)) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (Orb.n_mem_G hn')) hG1 hG2 hβ0 hβA
      hA1_def hΛ1 hP
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
