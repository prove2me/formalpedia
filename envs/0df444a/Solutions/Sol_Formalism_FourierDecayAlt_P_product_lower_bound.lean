-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.product_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:33.887811+00:00
-- url     : https://prove2.me/submissions/76f268d6-577a-49df-9269-7d31363a3d76

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_exists_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_norm_xOf_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cof_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_norm_cof_rest_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_remainder_norm_le_strict_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_rpow_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6 Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.ProdLower := by
  intro m Kc hK h0 R hR
  obtain ⟨d, hd, hD⟩ := exists_lower hK h0
  set R' : ℝ := max R 1 with hR'
  have hR1 : 1 ≤ R' := le_max_right _ _
  have hR0 : 0 < R' := lt_of_lt_of_le one_pos hR1
  set Cm : ℝ := ((m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) ^ m) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set Ce : ℝ := (m : ℝ) * ((m : ℝ) + 1) ^ m with hCe
  have hCe0 : 0 ≤ Ce := by positivity
  set q : ℝ := d / (2 * (Cm + Ce + 1) * R' ^ (m + 2)) with hq
  have hq0 : 0 < q := by positivity
  refine ⟨min 1 (q ^ 2), d / (2 * R' ^ (m + 1)), by positivity, by positivity, ?_⟩
  intro ε hε hε2 D hDK t ht htle X B ρ₁ ρ' σ hS hX hB hρ₁ hρ' hσ hrel
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hT1 : ‖t‖ ≤ 1 := le_trans htle (min_le_left _ _)
  have hTq : ‖t‖ ≤ q ^ 2 := le_trans htle (min_le_right _ _)
  set W : ℝ := ‖t‖ ^ (-ε) with hW
  have hW1 : 1 ≤ W := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hT hT1 (by linarith)
  have hW0 : 0 < W := lt_of_lt_of_le one_pos hW1
  set L : ℝ := R' * W with hLdef
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hR1 hW1
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hRL : R * W ≤ L := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0.le
  have hX' : ∀ i j, ‖X i j‖ ≤ L := fun i j => (hX i j).trans hRL
  have hB' : ∀ i, ‖B i‖ ≤ L := fun i => (hB i).trans hRL
  have hρ'' : ∀ k, ‖ρ' k‖ ≤ L := fun k => (hρ' k).trans hRL
  have hsq : L ^ (m + 2) * ‖t‖ ≤ R' ^ (m + 2) * q := by
    rw [hLdef, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (le_trans (rpow_bound m hT hT1 hε2) (Real.sqrt_le_iff.mpr ⟨hq0.le, hTq⟩)) (by positivity)
  have hRb := remainder_norm_le_strict_upper (t := t) hL hT1 hS hX' hB' hρ''
  set P : ℂ := ∏ k, xOf X B k with hP
  set E : ℂ := ∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j) with hE
  have hCof : Cof X B t = E + (-1) ^ m * P := cof_split hS B t
  have hEb : ‖E‖ ≤ Ce * (L ^ (m + 1) * ‖t‖) := norm_cof_rest_le hL hT1 hX' hB'
  have hEρ : ‖E * ρ₁‖ ≤ Ce * (L ^ (m + 2) * ‖t‖) := by
    rw [norm_mul]
    calc ‖E‖ * ‖ρ₁‖ ≤ (Ce * (L ^ (m + 1) * ‖t‖)) * L :=
          mul_le_mul hEb (hρ₁.trans hRL) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h1 : ‖t ^ (m + 1) * σ‖ ≤ L ^ (m + 2) * ‖t‖ := by
    rw [norm_mul, norm_pow, mul_comm]
    refine mul_le_mul (le_trans (hσ.trans hRL) (le_self_pow₀ hL (by omega)))
      (pow_le_of_le_one hT.le hT1 (by omega)) (by positivity) (by positivity)
  have h2 : ‖(-1) ^ m * P * ρ₁‖ ≤ ‖P‖ * L := by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact mul_le_mul_of_nonneg_left (hρ₁.trans hRL) (norm_nonneg _)
  have hDeq : D = t ^ (m + 1) * σ - (-1) ^ m * P * ρ₁ - E * ρ₁ - R0 X B ρ' t := by
    rw [hrel, hCof]; ring
  have h3 : ‖D‖ ≤ L ^ (m + 2) * ‖t‖ + ‖P‖ * L + Ce * (L ^ (m + 2) * ‖t‖) + Cm * (L ^ (m + 2) * ‖t‖) := by
    calc ‖D‖ = ‖t ^ (m + 1) * σ - (-1) ^ m * P * ρ₁ - E * ρ₁ - R0 X B ρ' t‖ := by rw [← hDeq]
      _ ≤ ‖t ^ (m + 1) * σ‖ + ‖(-1) ^ m * P * ρ₁‖ + ‖E * ρ₁‖ + ‖R0 X B ρ' t‖ := by
          refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
          refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
          exact norm_sub_le _ _
      _ ≤ _ := add_le_add (add_le_add (add_le_add h1 h2) hEρ) hRb
  have h4 : (Cm + Ce + 1) * (L ^ (m + 2) * ‖t‖) ≤ d / 2 := by
    calc (Cm + Ce + 1) * (L ^ (m + 2) * ‖t‖) ≤ (Cm + Ce + 1) * (R' ^ (m + 2) * q) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = d / 2 := by rw [hq]; field_simp
  have h5 : d / 2 ≤ ‖P‖ * L := by
    have := hD D hDK
    linarith
  have hRpow : 0 < R' ^ (m + 1) := by positivity
  constructor
  · have hinv : ‖t‖ ^ ε = W⁻¹ := by rw [hW, Real.rpow_neg hT.le, inv_inv]
    rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hW0, div_le_iff₀ (by positivity)]
    have h6 : R' ≤ R' ^ (m + 1) := le_self_pow₀ hR1 (by omega)
    have h7 : ‖P‖ * L ≤ ‖P‖ * W * R' ^ (m + 1) := by
      rw [hLdef, mul_assoc, mul_comm R' W]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 hW0.le) (norm_nonneg _)
    linarith
  · intro k
    have h6 : ‖P‖ ≤ ‖xOf X B k‖ * L ^ m := by
      rw [hP, ← Finset.mul_prod_erase Finset.univ (fun k => xOf X B k) (Finset.mem_univ k), norm_mul,
        norm_prod]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ∏ l ∈ Finset.univ.erase k, ‖xOf X B l‖ ≤ ∏ _l ∈ Finset.univ.erase k, L :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => norm_xOf_le hX' hB' l
        _ = L ^ m := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
              Fintype.card_fin, Nat.add_sub_cancel]
    have h7 : d / 2 ≤ ‖xOf X B k‖ * (R' ^ (m + 1) * W ^ (m + 1)) := by
      calc d / 2 ≤ ‖P‖ * L := h5
        _ ≤ ‖xOf X B k‖ * L ^ m * L := mul_le_mul_of_nonneg_right h6 hL0.le
        _ = _ := by rw [hLdef]; ring
    have h8 : ‖t‖ ^ (((m : ℝ) + 2) * ε) ≤ (W ^ (m + 1))⁻¹ := by
      have e : (W ^ (m + 1))⁻¹ = ‖t‖ ^ (((m : ℝ) + 1) * ε) := by
        rw [hW, ← Real.rpow_natCast, ← Real.rpow_mul hT.le, ← Real.rpow_neg hT.le]
        congr 1
        push_cast
        ring
      rw [e]
      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (mul_le_mul_of_nonneg_right (by linarith) hε.le)
    have hWp : 0 < W ^ (m + 1) := by positivity
    calc d / (2 * R' ^ (m + 1)) * ‖t‖ ^ (((m : ℝ) + 2) * ε)
        ≤ d / (2 * R' ^ (m + 1)) * (W ^ (m + 1))⁻¹ := mul_le_mul_of_nonneg_left h8 (by positivity)
      _ ≤ ‖xOf X B k‖ := by
          rw [← div_eq_mul_inv, div_le_iff₀ hWp, div_le_iff₀ (by positivity)]
          linarith
end Formalism.FourierDecayAlt.P
