-- Prove2me | solution 1 for ConnesGreen.canonical_negative_background_custody
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T04:25:01.648514+00:00
-- url     : https://prove2.me/submissions/c1bfd496-1c50-4f45-a977-ef67ba10d3fb

import Definitions.Def_ConnesGreen_actual_pair_columns
import Theorems.Thm_ConnesGreen_canonical_Green_realization_and_synthesis
import Theorems.Thm_ConnesRZNative_bounded_column_synthesis_with_adjoint_energy
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical
noncomputable section

private theorem weighted_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v : CriticalZeros → H) (ρ : CriticalZeros) :
    ‖weightedGreenColumn v ρ‖ ^ 2 = (zeroMult ρ.1 : ℝ) * ‖v ρ‖ ^ 2 := by
  simp [weightedGreenColumn, norm_smul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

private theorem pair_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v : CriticalZeros → H) (ρ : CriticalZeros) :
    ‖positiveGreenColumn v ρ‖ ^ 2 + ‖negativeGreenColumn v ρ‖ ^ 2 =
      (‖weightedGreenColumn v ρ‖ ^ 2 + ‖weightedGreenColumn v (reflectedZero ρ)‖ ^ 2) / 2 := by
  have hp := parallelogram_law_with_norm ℂ (weightedGreenColumn v ρ)
    (weightedGreenColumn v (reflectedZero ρ))
  unfold positiveGreenColumn negativeGreenColumn
  simp only [norm_smul, mul_pow]
  norm_num
  nlinarith [hp]

private theorem actual_negative_columns_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun ρ => ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ‖ ^ 2) := by
  have hall := canonical_Green_realization_and_synthesis t ht
  let v := fun τ => sourceEmbed t (actualGreenSource τ)
  have hs : Summable (fun ρ => ‖weightedGreenColumn v ρ‖ ^ 2) := by
    have he : (fun ρ => ‖weightedGreenColumn v ρ‖ ^ 2) = weightedEnergy t := by
      funext ρ
      rw [weighted_norm]
      change (zeroMult ρ.1 : ℝ) * ‖sourceEmbed t (actualGreenSource ρ)‖ ^ 2 = _
      rw [(hall.2.1 ρ).2.2.2.2]
      rfl
    rw [he]
    exact hall.2.2.2.1
  have hr : Summable (fun ρ : CriticalZeros => ‖weightedGreenColumn v (reflectedZero ρ)‖ ^ 2) :=
    hs.comp_injective (fun a b h => by
      have hh := congrArg reflectedZero h
      simpa only [reflectedZero_involutive] using hh)
  have hb : Summable (fun ρ => ‖positiveGreenColumn v ρ‖ ^ 2 + ‖negativeGreenColumn v ρ‖ ^ 2) := by
    have he : (fun ρ => ‖positiveGreenColumn v ρ‖ ^ 2 + ‖negativeGreenColumn v ρ‖ ^ 2) =
        fun ρ => (‖weightedGreenColumn v ρ‖ ^ 2 + ‖weightedGreenColumn v (reflectedZero ρ)‖ ^ 2) / 2 := by
      funext ρ
      exact pair_norm v ρ
    rw [he]
    exact (hs.add hr).div_const 2
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun _ => le_add_of_nonneg_left (sq_nonneg _)) hb

theorem solution (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ∃ N : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
    ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, N (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ h ρ, (ContinuousLinearMap.adjoint B) h ρ =
        ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1, h⟫_ℂ) ∧
      (∀ h, ‖(ContinuousLinearMap.adjoint M) h‖ ^ 2 +
        ‖(ContinuousLinearMap.adjoint B) h‖ ^ 2 = ‖(ContinuousLinearMap.adjoint N) h‖ ^ 2) ∧
      N ∘L N.adjoint = M ∘L M.adjoint + B ∘L B.adjoint ∧
      (B ∘L B.adjoint).IsPositive ∧
      (∀ T : ℓ²({ρ : CriticalZeros // ρ ∉ S}, ℂ) →L[ℂ] Physical t,
        (∀ ρ, T (lp.single 2 ρ (1 : ℂ)) =
          negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) → T = B) := by
  let v := negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ))
  have hs := actual_negative_columns_summable t ht
  obtain ⟨N, _, hNb, _, hNn, _, _⟩ :=
    ConnesRZNative.bounded_column_synthesis_with_adjoint_energy v hs
  obtain ⟨M, _, hMb, _, hMn, _, _⟩ :=
    ConnesRZNative.bounded_column_synthesis_with_adjoint_energy
      (fun ρ : {ρ : CriticalZeros // ρ ∈ S} => v ρ.1) (hs.comp_injective Subtype.val_injective)
  obtain ⟨B, _, hBb, hBc, hBn, _, hBu⟩ :=
    ConnesRZNative.bounded_column_synthesis_with_adjoint_energy
      (fun ρ : {ρ : CriticalZeros // ρ ∉ S} => v ρ.1) (hs.comp_injective Subtype.val_injective)
  have hpart : ∀ h, ‖(ContinuousLinearMap.adjoint M) h‖ ^ 2 +
      ‖(ContinuousLinearMap.adjoint B) h‖ ^ 2 = ‖(ContinuousLinearMap.adjoint N) h‖ ^ 2 := by
    intro h
    rw [hMn, hBn, hNn]
    have hi : Summable (fun ρ : CriticalZeros => ‖⟪v ρ, h⟫_ℂ‖ ^ 2) := by
      apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
        (fun ρ => ?_) (hs.mul_right (‖h‖ ^ 2))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (norm_inner_le_norm (𝕜 := ℂ) (v ρ) h) 2
    exact hi.tsum_subtype_add_tsum_subtype_compl (S : Set CriticalZeros)
  refine ⟨N, M, B, ?_, ?_, ?_, hBc, hpart, ?_,
    ContinuousLinearMap.isPositive_self_comp_adjoint B, ?_⟩
  · intro ρ
    convert hNb ρ using 1
    congr 1
    ext τ
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> rfl
  · intro ρ
    convert hMb ρ using 1
    congr 1
    ext τ
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> rfl
  · intro ρ
    convert hBb ρ using 1
    congr 1
    ext τ
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> rfl
  · have he := (ext_inner_map (N ∘L N.adjoint).toLinearMap
        (M ∘L M.adjoint + B ∘L B.adjoint).toLinearMap).mp (fun h => by
          simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.add_apply, inner_add_left]
          rw [← ContinuousLinearMap.adjoint_inner_right N (N.adjoint h) h,
            ← ContinuousLinearMap.adjoint_inner_right M (M.adjoint h) h,
            ← ContinuousLinearMap.adjoint_inner_right B (B.adjoint h) h]
          simp only [inner_self_eq_norm_sq_to_K]
          exact_mod_cast (hpart h).symm)
    apply ContinuousLinearMap.ext
    intro h
    exact LinearMap.congr_fun he h
  · intro T hc
    apply hBu T
    intro ρ
    convert hc ρ using 1
    congr 1
    ext τ
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> rfl
