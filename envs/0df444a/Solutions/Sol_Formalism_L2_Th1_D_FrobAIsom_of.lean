-- Prove2me | solution 1 for Formalism.L2.Th1.D.FrobAIsom_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:50.132793+00:00
-- url     : https://prove2.me/submissions/cd189e8a-8ea1-4f08-b220-0a737289ea8b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_norm_pow_add_eq_one
import Theorems.Thm_Formalism_L2_Th1_D_KF_norm_pow_add_lt_one
import Theorems.Thm_Formalism_L2_Th1_D_KF_norm_eq_of_pow_sub

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
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open KF
namespace Formalism.L2.Th1.D
theorem _root_.solution : RingAFacts → FrobAIsom := by
  intro hA l hl σ0 hσ
  obtain ⟨hle, hpow⟩ := hA l
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  have hl0 : (l : ℝ) ≠ 0 := hlpos.ne'

  have hform : ∀ x : ringA l, ∃ y : ringA l,
      ((σ0 x : ringA l) : ℂ_[l]) = (x : ℂ_[l]) ^ l + (l : ℂ_[l]) * (y : ℂ_[l]) := by
    intro x
    obtain ⟨y, hy⟩ := hσ x
    refine ⟨y, ?_⟩
    have h := congrArg Subtype.val hy
    push_cast at h
    linear_combination h
  have hsm : ∀ x : ringA l, ‖(x : ℂ_[l])‖ < 1 → ‖((σ0 x : ringA l) : ℂ_[l])‖ < 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hform x
    rw [hy]
    exact norm_pow_add_lt_one hx (hle _ y.2)
  have hun : ∀ x : ringA l, ‖(x : ℂ_[l])‖ = 1 → ‖((σ0 x : ringA l) : ℂ_[l])‖ = 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hform x
    rw [hy]
    exact norm_pow_add_eq_one hx (hle _ y.2)

  have hrel : ∀ x : ringA l, ‖(x : ℂ_[l])‖ < 1 → ∃ y : ringA l,
      ‖(x : ℂ_[l])‖ = (l : ℝ)⁻¹ * ‖(y : ℂ_[l])‖ ∧
      ‖((σ0 x : ringA l) : ℂ_[l])‖ = (l : ℝ)⁻¹ * ‖((σ0 y : ringA l) : ℂ_[l])‖ := by
    intro x hx
    obtain ⟨f, hf, y, hy, hxy⟩ := hpow (x : ℂ_[l]) x.2
    have hN : l ^ f - 1 ≠ 0 := by
      have : 2 ≤ l ^ f := le_trans hl.out.two_le (Nat.le_self_pow hf.ne' l)
      omega
    have hN1 : l ^ f - 1 + 1 = l ^ f := Nat.sub_add_cancel (Nat.one_le_pow _ _ hl.out.pos)
    have e : x ^ (l ^ f) - x = (l : ringA l) * ⟨y, hy⟩ := Subtype.ext (by push_cast; exact hxy)
    have e2 := congrArg (fun z => ((σ0 z : ringA l) : ℂ_[l])) e
    simp only [map_sub, map_pow, map_mul, map_natCast] at e2
    push_cast at e2
    refine ⟨⟨y, hy⟩, ?_, ?_⟩
    · apply norm_eq_of_pow_sub hN hx
      rw [hN1]
      exact hxy
    · apply norm_eq_of_pow_sub hN (hsm x hx)
      rw [hN1]
      exact e2

  have key : ∀ k : ℕ, ∀ x : ringA l, ((l : ℝ)⁻¹) ^ k < l * ‖(x : ℂ_[l])‖ →
      ‖((σ0 x : ringA l) : ℂ_[l])‖ = ‖(x : ℂ_[l])‖ := by
    intro k
    induction k with
    | zero =>
      intro x hx
      rcases (hle _ x.2).lt_or_eq with h | h
      · exfalso
        obtain ⟨y, hy1, -⟩ := hrel x h
        have hy := hle _ y.2
        rw [pow_zero] at hx
        have hxy : (l : ℝ) * ‖(x : ℂ_[l])‖ = ‖(y : ℂ_[l])‖ := by
          rw [hy1]
          field_simp
        linarith
      · rw [h]
        exact hun x h
    | succ k ih =>
      intro x hx
      rcases (hle _ x.2).lt_or_eq with h | h
      · obtain ⟨y, hy1, hy2⟩ := hrel x h
        have hyx : ‖(y : ℂ_[l])‖ = l * ‖(x : ℂ_[l])‖ := by
          rw [hy1]
          field_simp
        have hk : ((l : ℝ)⁻¹) ^ k < l * ‖(y : ℂ_[l])‖ := by
          rw [hyx]
          rw [pow_succ] at hx
          have h2 := mul_lt_mul_of_pos_left hx hlpos
          calc ((l : ℝ)⁻¹) ^ k = l * (((l : ℝ)⁻¹) ^ k * (l : ℝ)⁻¹) := by field_simp
            _ < l * (l * ‖(x : ℂ_[l])‖) := h2
        rw [hy2, ih y hk, hy1]
      · rw [h]
        exact hun x h
  intro x
  by_cases hx0 : ‖(x : ℂ_[l])‖ = 0
  · have hx : x = 0 := Subtype.ext (by simpa using hx0)
    subst hx
    simp
  · have hpos : 0 < (l : ℝ) * ‖(x : ℂ_[l])‖ :=
      mul_pos hlpos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0))
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
    exact key k x hk
end Formalism.L2.Th1.D
