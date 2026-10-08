-- Prove2me | solution 1 for ConnesGreen.actual_zero_lower_bound_iff_finite_restoration
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T16:35:02.73462+00:00
-- url     : https://prove2.me/submissions/f4502262-2c53-473b-9e08-9115267cd07f

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
      (∀ ε : ℝ, 0 < ε → ∀ a : ℝ,
        (a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
          ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ marker (P ∘L P.adjoint + ε • 1) M ↔
        ∀ α : ℝ, 0 < α → α < 1 →
          ∃ F : Finset CriticalZeros, S ⊆ F ∧
          ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
            (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
              negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
            ‖B ∘L B.adjoint‖ ≤ α * ε ∧
            (a - α) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
              ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤
              marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M)) := by
  obtain ⟨P, M, hPb, hMb, hrec⟩ := ConnesGreen.actual_zero_diagonal_marker_recovery t ht S
  refine ⟨P, M, hPb, hMb, ?_⟩
  intro ε hε a
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
      (a - α) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) = a • 1 - α • 1 :=
          sub_smul a α (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
            ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
      _ ≤ marker (P ∘L P.adjoint + ε • 1) M - α • 1 := sub_le_sub_right hhalf _
      _ ≤ marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M :=
        (sub_le_iff_le_add).mpr hg
  · intro hfinite
    let b : ℕ → ℝ := fun n => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))
    have hap : ∀ n, 0 < b n := by intro n; dsimp [b]; positivity
    have ha1 : ∀ n, b n < 1 := by
      intro n
      have hc : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        linarith [Nat.cast_nonneg (α := ℝ) n]
      dsimp [b]
      linarith
    have ha0 : Tendsto b atTop (𝓝 0) := by
      have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [b] using hc.const_mul (1 / 2 : ℝ)
    have hlim : Tendsto (fun n => (a - b n) •
        (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
          ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))) atTop
        (𝓝 (a • 1)) := by
      simpa using (tendsto_const_nhds.sub ha0).smul_const
        (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
          ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
    apply le_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    obtain ⟨F, _, B, _, htail, hhalf⟩ := hfinite (b n) (hap n) (ha1 n)
    have hL : 0 ≤ P ∘L P.adjoint :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_self_comp_adjoint P)
    have hR : 0 ≤ B ∘L B.adjoint :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_self_comp_adjoint B)
    have hdiff := (WeilDefect.MarkerStability.tail_marker_stability
      (P ∘L P.adjoint) (B ∘L B.adjoint) M hL hR ε (b n) hε
      (hap n).le (ha1 n) htail).2.1
    exact hhalf.trans (sub_nonneg.mp hdiff)
