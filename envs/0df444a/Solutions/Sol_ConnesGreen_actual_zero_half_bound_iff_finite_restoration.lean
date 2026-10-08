-- Prove2me | solution 1 for ConnesGreen.actual_zero_half_bound_iff_finite_restoration
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T05:34:50.451991+00:00
-- url     : https://prove2.me/submissions/6a6f21c7-1d64-492c-9460-228c5cf8c88f

import Theorems.Thm_ConnesGreen_actual_zero_diagonal_marker_recovery
import Theorems.Thm_WeilDefect_MarkerStability_tail_marker_stability
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem solution (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ ε : ℝ, 0 < ε →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
          ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ marker (P ∘L P.adjoint + ε • 1) M ↔
        ∀ α : ℝ, 0 < α → α < 1 →
          ∃ F : Finset CriticalZeros, S ⊆ F ∧
          ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
            (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
              negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
            ‖B ∘L B.adjoint‖ ≤ α * ε ∧
            (1 / 2 - α) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
              ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤
              marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M)) := by
  obtain ⟨P, M, hPb, hMb, hrec⟩ := ConnesGreen.actual_zero_diagonal_marker_recovery t ht S
  refine ⟨P, M, hPb, hMb, ?_⟩
  intro ε hε
  constructor
  · intro hhalf α hα hα1
    obtain ⟨F, hinc, B, hBb, htail, _, hdiff, hnorm⟩ := hrec ε hε α hα hα1
    have hbound := (CStarAlgebra.norm_le_iff_le_algebraMap _ hα.le hdiff).mp hnorm
    rw [Algebra.algebraMap_eq_smul_one] at hbound
    have hg : marker (P ∘L P.adjoint + ε • 1) M ≤
        marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M + α • 1 := by
      simpa only [add_comm] using (sub_le_iff_le_add).mp hbound
    refine ⟨F, hinc, B, hBb, htail, ?_⟩
    calc
      (1 / 2 - α) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) = (1 / 2 : ℝ) • 1 - α • 1 :=
          sub_smul (1 / 2 : ℝ) α (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
            ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
      _ ≤ marker (P ∘L P.adjoint + ε • 1) M - α • 1 := sub_le_sub_right hhalf _
      _ ≤ marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M :=
        (sub_le_iff_le_add).mpr hg
  · intro hfinite
    let a : ℕ → ℝ := fun n => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))
    have hap : ∀ n, 0 < a n := by intro n; dsimp [a]; positivity
    have ha1 : ∀ n, a n < 1 := by
      intro n
      have hc : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        linarith [Nat.cast_nonneg (α := ℝ) n]
      dsimp [a]
      linarith
    have ha0 : Tendsto a atTop (𝓝 0) := by
      have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [a] using hc.const_mul (1 / 2 : ℝ)
    have hlim : Tendsto (fun n => (1 / 2 - a n) •
        (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
          ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))) atTop
        (𝓝 ((1 / 2 : ℝ) • 1)) := by
      simpa using (tendsto_const_nhds.sub ha0).smul_const
        (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
          ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
    apply le_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    obtain ⟨F, _, B, _, htail, hhalf⟩ := hfinite (a n) (hap n) (ha1 n)
    have hL : 0 ≤ P ∘L P.adjoint :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_self_comp_adjoint P)
    have hR : 0 ≤ B ∘L B.adjoint :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_self_comp_adjoint B)
    have hdiff := (WeilDefect.MarkerStability.tail_marker_stability
      (P ∘L P.adjoint) (B ∘L B.adjoint) M hL hR ε (a n) hε
      (hap n).le (ha1 n) htail).2.1
    exact hhalf.trans (sub_nonneg.mp hdiff)
