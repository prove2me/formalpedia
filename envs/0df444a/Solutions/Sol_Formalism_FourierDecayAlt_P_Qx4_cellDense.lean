-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.cellDense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:48:09.08315+00:00
-- url     : https://prove2.me/submissions/667ad59f-f2ff-4788-8d47-44c1a1c4feda

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_sub_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hs_act
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Hh
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_herm_e_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_herm_es_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_e_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_es_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_h_e_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_herm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hs_glev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_ne_of_val_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hs_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_zero_mem_closure_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_herm_H_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_self_im
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Hpk_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_self_im
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq
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
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution : CellDense := by
  intro k r l g hg
  by_cases hc : herm (Hpk k r) (g *ᵥ bvec (eI k r l)) (bvec (eI k r l)) = 0
  swap
  · exact subset_closure ⟨hg, hc⟩
  set x := g⁻¹ *ᵥ bvec (eI k r l) with hx
  set α := herm (Hpk k r) x (bvec (esI k r l)) with hα
  set x₀ := x - α • bvec (eI k r l) with hx₀
  set v₀ := Hpk k r *ᵥ x₀ with hv₀
  set q := herm (Hpk k r) v₀ v₀ with hq
  set κ := Complex.I - q / 2 with hκ
  have hex : herm (Hpk k r) (bvec (eI k r l)) x = 0 := by rw [hx, ← uh_herm_inv hg.1, hc]
  have hxe : herm (Hpk k r) x (bvec (eI k r l)) = 0 := by rw [← h_conj _ Hh, hex, map_zero]
  have hve : herm (Hpk k r) v₀ (bvec (eI k r l)) = 0 := by
    rw [hv₀, herm_H_bvec, ← herm_es_right x₀ l, hx₀, h_sub_left, h_smul_left, h_e_es, if_pos rfl, ← hα]; ring
  have hvs : herm (Hpk k r) v₀ (bvec (esI k r l)) = 0 := by
    rw [hv₀, herm_H_bvec, ← herm_e_right x₀ l, hx₀, h_sub_left, h_smul_left, h_e_e, hxe]; ring
  have hev : herm (Hpk k r) (bvec (eI k r l)) v₀ = 0 := by rw [← h_conj _ Hh, hve, map_zero]
  have hva : ∀ a : Fin r, a.val < (l.castSucc).val →
      herm (Hpk k r) (bvec (eI k r a)) v₀ = 0 ∧ herm (Hpk k r) (bvec (esI k r a)) v₀ = 0 := by
    intro a ha
    have hne : a ≠ l := ne_of_val_lt (by simpa using ha)
    have hgi := glev_inv hg
    constructor
    · rw [← h_conj _ Hh, hv₀, herm_H_bvec, ← herm_es_right x₀ a, hx₀, h_sub_left, h_smul_left, h_e_es, if_neg (Ne.symm hne), hx]
      conv_lhs => rw [← (hgi.2 a ha).2]
      rw [uh_herm hgi.1, h_e_es, if_neg (Ne.symm hne)]; simp
    · rw [← h_conj _ Hh, hv₀, herm_H_bvec, ← herm_e_right x₀ a, hx₀, h_sub_left, h_smul_left, h_e_e, hx]
      conv_lhs => rw [← (hgi.2 a ha).1]
      rw [uh_herm hgi.1, h_e_e]; simp
  have hqc : conj q = q := h_conj _ Hh _ _
  have hκ0 : κ ≠ 0 := by
    intro h
    have h1 := congrArg Complex.im h
    have h2 : q.im = 0 := B2x8.herm_self_im k r v₀
    simp [hκ, h2] at h1
  set A := herm (Hpk k r) v₀ x with hA
  set B := κ * conj α with hB
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_cases h0 : x₀ = 0
    · right
      have hα0 : α ≠ 0 := by
        intro h
        have hx0 : x = 0 := by
          have : x = x₀ + α • bvec (eI k r l) := by rw [hx₀]; simp
          rw [this, h0, h]; simp
        have h1 : g *ᵥ x = bvec (eI k r l) := by
          rw [hx, Matrix.mulVec_mulVec, uh_mul_inv hg.1, Matrix.one_mulVec]
        rw [hx0, Matrix.mulVec_zero] at h1
        have h2 := congrFun h1 (eI k r l)
        simp [bvec] at h2
      exact mul_ne_zero hκ0 ((map_ne_zero _).2 hα0)
    · left
      have h1 : A = star x₀ ⬝ᵥ x₀ := by
        have : x = x₀ + α • bvec (eI k r l) := by rw [hx₀]; simp
        rw [hA, this, h_add_right, h_smul_right, hve, mul_zero, add_zero, hv₀]
        unfold herm
        rw [Matrix.mulVec_mulVec, B2x8.Hpk_sq, Matrix.one_mulVec]
      rw [h1]
      intro h2
      exact h0 (dotProduct_star_self_eq_zero.mp h2)
  let γ : ℝ → Mx k r := fun t => g * hs (Hpk k r) (bvec (esI k r l)) ((t : ℂ) • v₀) ((t : ℂ) ^ 2 * κ)
  have hγc : Continuous γ := by
    have : γ = fun t : ℝ => g * (1 + (t : ℂ) • (Matrix.vecMulVec v₀ (fun j => herm (Hpk k r) (bvec j) (bvec (esI k r l))) -
        Matrix.vecMulVec (bvec (esI k r l)) (fun j => herm (Hpk k r) (bvec j) v₀)) +
        ((t : ℂ) ^ 2 * κ) • Matrix.vecMulVec (bvec (esI k r l)) (fun j => herm (Hpk k r) (bvec j) (bvec (esI k r l)))) := by
      funext t; simp only [γ]; rw [hs_poly]
    rw [this]
    fun_prop
  have hγ0 : γ 0 = g := by
    simp only [γ]; rw [hs_poly]; simp
  rw [← hγ0]
  refine map_mem_closure hγc (zero_mem_closure_poly hAB) ?_
  intro t ht
  have hk : hs (Hpk k r) (bvec (esI k r l)) ((t : ℂ) • v₀) ((t : ℂ) ^ 2 * κ) ∈ Glev k r l.castSucc := by
    apply hs_glev (h_es_es l l)
    · rw [h_smul_left, hvs, mul_zero]
    · rw [h_smul_left, h_smul_right, ← hq, map_mul, map_pow, Complex.conj_ofReal, hκ, map_sub, map_div₀, hqc,
        Complex.conj_I]
      simp only [map_ofNat]
      ring
    · intro a ha
      have hne : a ≠ l := ne_of_val_lt (by simpa using ha)
      exact ⟨by rw [h_e_es, if_neg hne], h_es_es a l⟩
    · intro a ha
      rw [h_smul_right, h_smul_right, (hva a ha).1, (hva a ha).2]
      simp
  refine ⟨glev_mul hg hk, ?_⟩
  show herm (Hpk k r) (γ t *ᵥ bvec (eI k r l)) (bvec (eI k r l)) ≠ 0
  have : herm (Hpk k r) (γ t *ᵥ bvec (eI k r l)) (bvec (eI k r l)) = (t : ℂ) * (A + t * B) := by
    simp only [γ]
    rw [← Matrix.mulVec_mulVec, uh_herm_inv hg.1, ← hx, hs_act, h_smul_right, hev, h_e_es, if_pos rfl]
    simp only [h_add_left, h_sub_left, h_smul_left, hex, ← hA]
    rw [← h_conj _ Hh x, ← hα, hB]
    ring
  rw [this]
  exact ht
end Formalism.FourierDecayAlt.P.Qx4
