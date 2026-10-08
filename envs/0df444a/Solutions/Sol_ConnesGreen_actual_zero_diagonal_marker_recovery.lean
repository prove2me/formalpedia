-- Prove2me | solution 1 for ConnesGreen.actual_zero_diagonal_marker_recovery
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T05:29:24.778189+00:00
-- url     : https://prove2.me/submissions/b490dd83-56c5-4bc7-a831-ce528e171dd9

import Definitions.Def_ConnesGreen_actual_pair_columns
import Definitions.Def_WeilMarker_regularized_cost
import Theorems.Thm_ConnesGreen_canonical_Green_realization_and_synthesis
import Theorems.Thm_ConnesGreen_canonical_negative_background_custody
import Theorems.Thm_ConnesRZNative_bounded_column_synthesis_with_adjoint_energy
import Theorems.Thm_WeilDefect_MarkerStability_tail_marker_stability
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative
open WeilDefect.MarkerStability Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
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

private theorem actual_actor_columns_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun ρ => ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ‖ ^ 2) ∧
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
  exact ⟨Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun _ => le_add_of_nonneg_right (sq_nonneg _)) hb,
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun _ => le_add_of_nonneg_left (sq_nonneg _)) hb⟩


theorem solution (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ ε : ℝ, 0 < ε → ∀ α : ℝ, 0 < α → α < 1 →
        ∃ F : Finset CriticalZeros, S ⊆ F ∧
        ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
          (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
            negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
          ‖B ∘L B.adjoint‖ ≤ α * ε ∧
          IsStrictlyPositive (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) ∧
          0 ≤ marker (P ∘L P.adjoint + ε • 1) M -
            marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M ∧
          ‖marker (P ∘L P.adjoint + ε • 1) M -
            marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M‖ ≤ α) := by
  obtain ⟨hp, hn⟩ := actual_actor_columns_summable t ht
  let v := negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ))
  obtain ⟨P, _, hPb, _, _, _, _⟩ :=
    ConnesRZNative.bounded_column_synthesis_with_adjoint_energy
      (positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ))) hp
  obtain ⟨_, M, _, _, hMb, _, _, _, _, _, _⟩ :=
    ConnesGreen.canonical_negative_background_custody t ht S
  refine ⟨P, M, ?_, ?_, ?_⟩
  · intro ρ
    convert hPb ρ using 1
    congr 1
    ext τ
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> rfl
  · exact hMb
  · intro ε hε α hα hα1
    have htail := (tendsto_order.mp (tendsto_tsum_compl_atTop_zero
      (fun ρ => ‖v ρ‖ ^ 2))).2 (α * ε) (mul_pos hα hε)
    obtain ⟨F, hinc, hF⟩ := ((eventually_ge_atTop S).and htail).exists
    obtain ⟨B, _, hBb, _, _, hBn, _⟩ :=
      ConnesRZNative.bounded_column_synthesis_with_adjoint_energy
        (fun ρ : {ρ : CriticalZeros // ρ ∉ F} => v ρ.1) (hn.comp_injective Subtype.val_injective)
    have hcomp := ContinuousLinearMap.opNorm_comp_le B B.adjoint
    rw [ContinuousLinearMap.adjoint.norm_map, ← pow_two] at hcomp
    have hnorm : ‖B ∘L B.adjoint‖ ≤ α * ε := (hcomp.trans hBn).trans hF.le
    have hL : 0 ≤ P ∘L P.adjoint :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_self_comp_adjoint P)
    have hR : 0 ≤ B ∘L B.adjoint :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_self_comp_adjoint B)
    have hs := WeilDefect.MarkerStability.tail_marker_stability
      (P ∘L P.adjoint) (B ∘L B.adjoint) M hL hR ε α hε hα.le hα1 hnorm
    refine ⟨F, hinc, B, ?_, hnorm, hs⟩
    intro ρ
    convert hBb ρ using 1
    congr 1
    ext τ
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs <;> rfl
