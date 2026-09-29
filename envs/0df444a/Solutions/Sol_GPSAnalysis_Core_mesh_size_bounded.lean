-- Prove2me | solution 1 for GPSAnalysis.Core.mesh_size_bounded
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:18:17.79798+00:00
-- url     : https://prove2.me/submissions/74845f26-8445-497b-b42b-2e52cc1ec555

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run

namespace GPSAnalysis.Core

open Matrix

theorem aux_msb_Δpos {n m p : ℕ} {P : GPSSetup n m p} (R : GPSRun P) : ∀ k, 0 < R.Δ k := by
  intro k
  induction k with
  | zero => exact R.Δ_zero_pos
  | succ k ih =>
    rw [R.Δ_succ k]
    have hτ : (0:ℝ) < (P.τ : ℝ) := by
      have := P.one_lt_τ
      have h0 : (0:ℚ) < P.τ := lt_trans zero_lt_one this
      exact_mod_cast h0
    exact mul_pos (zpow_pos hτ _) ih

theorem aux_msb_opbound {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin n → ℝ, ‖G *ᵥ u‖ ≤ C * ‖u‖ := by
  let f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' G)
  refine ⟨‖f‖, norm_nonneg _, fun u => ?_⟩
  have := f.le_opNorm u
  simpa [f] using this

theorem aux_msb_step {n m p : ℕ} {P : GPSSetup n m p} (R : GPSRun P)
    (M : ℝ) (hM : ∀ k, ‖R.x k‖ ≤ M) :
    ∃ B : ℝ, ∀ k, ¬ R.meshLocalOpt k → R.Δ k ≤ B := by
  obtain ⟨C, hC0, hC⟩ := aux_msb_opbound P.G⁻¹
  refine ⟨2 * M * C, fun k hk => ?_⟩
  obtain ⟨⟨hmesh, _⟩, hlt, _, _⟩ := R.improved k hk
  obtain ⟨z, hz⟩ := hmesh
  set v : Fin n → ℝ := P.Zbar.map (fun z : ℤ => (z : ℝ)) *ᵥ (fun j => (z j : ℝ)) with hv
  have hDv : P.D *ᵥ (fun j => (z j : ℝ)) = P.G *ᵥ v := by
    simp [GPSSetup.D, dirMatrix, hv, Matrix.mulVec_mulVec]
  have hvint : ∀ i, v i = ((∑ j, P.Zbar i j * (z j : ℤ) : ℤ) : ℝ) := by
    intro i
    simp [hv, Matrix.mulVec, dotProduct]
  have hne : R.x (k+1) ≠ R.x k := by
    intro h
    rw [h] at hlt
    exact lt_irrefl _ hlt
  have hvne : v ≠ 0 := by
    intro h0
    apply hne
    rw [hz, hDv, h0]
    simp
  have hv1 : 1 ≤ ‖v‖ := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hvne (funext hcon)
    have h1 : (1:ℝ) ≤ |v i| := by
      rw [hvint i] at hi ⊢
      have hi' : (∑ j, P.Zbar i j * (z j : ℤ) : ℤ) ≠ 0 := by exact_mod_cast hi
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hi'
    calc (1:ℝ) ≤ |v i| := h1
      _ = ‖v i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖v‖ := norm_le_pi_norm v i
  have hinv : P.G⁻¹ *ᵥ (P.G *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ P.G_nonsingular, Matrix.one_mulVec]
  have hvC : ‖v‖ ≤ C * ‖P.G *ᵥ v‖ := by
    have := hC (P.G *ᵥ v)
    rwa [hinv] at this
  have hΔpos := aux_msb_Δpos R k
  have hdist : R.Δ k * ‖P.G *ᵥ v‖ ≤ 2 * M := by
    have hdiff : R.x (k+1) - R.x k = R.Δ k • (P.G *ᵥ v) := by
      rw [hz, hDv]; abel
    have h2 : ‖R.x (k+1) - R.x k‖ ≤ 2 * M := by
      calc ‖R.x (k+1) - R.x k‖ ≤ ‖R.x (k+1)‖ + ‖R.x k‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM _) (hM _)
        _ = 2 * M := by ring
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hΔpos] at h2
    exact h2
  calc R.Δ k = R.Δ k * 1 := by ring
    _ ≤ R.Δ k * ‖v‖ := by gcongr
    _ ≤ R.Δ k * (C * ‖P.G *ᵥ v‖) := by gcongr
    _ = C * (R.Δ k * ‖P.G *ᵥ v‖) := by ring
    _ ≤ C * (2 * M) := by gcongr
    _ = 2 * M * C := by ring

end GPSAnalysis.Core

open GPSAnalysis.Core

theorem solution {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA3 : AssumptionA3 R) :
    ∃ r : ℕ, 0 < r ∧ ∀ k, R.Δ k ≤ R.Δ 0 * (P.τ : ℝ) ^ r := by
  obtain ⟨X, hXc, hX⟩ := hA3
  obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le.mp hXc.isBounded)
  obtain ⟨B, hB⟩ := aux_msb_step R M (fun k => hM _ (hX k))
  have hτ1 : (1:ℝ) < (P.τ : ℝ) := by exact_mod_cast P.one_lt_τ
  have hτ0 : (0:ℝ) < (P.τ : ℝ) := lt_trans zero_lt_one hτ1
  set Bmax := max (R.Δ 0) ((P.τ:ℝ) ^ P.wplus * B) with hBmax
  have hbound : ∀ k, R.Δ k ≤ Bmax := by
    intro k
    induction k with
    | zero => exact le_max_left _ _
    | succ k ih =>
      rw [R.Δ_succ k]
      by_cases hk : R.meshLocalOpt k
      · obtain ⟨_, _, _, hw⟩ := R.localOpt k hk
        have h1 : (P.τ:ℝ) ^ (R.w k) ≤ 1 := zpow_le_one_of_nonpos₀ hτ1.le (by omega)
        calc (P.τ:ℝ) ^ (R.w k) * R.Δ k ≤ 1 * R.Δ k :=
              mul_le_mul_of_nonneg_right h1 (aux_msb_Δpos R k).le
          _ = R.Δ k := one_mul _
          _ ≤ Bmax := ih
      · obtain ⟨_, _, _, hw⟩ := R.improved k hk
        have h1 : (P.τ:ℝ) ^ (R.w k) ≤ (P.τ:ℝ) ^ P.wplus := zpow_le_zpow_right₀ hτ1.le hw
        have h2 := hB k hk
        calc (P.τ:ℝ) ^ (R.w k) * R.Δ k ≤ (P.τ:ℝ) ^ P.wplus * B :=
              mul_le_mul h1 h2 (aux_msb_Δpos R k).le (zpow_pos hτ0 _).le
          _ ≤ Bmax := le_max_right _ _
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (Bmax / R.Δ 0) hτ1
  refine ⟨N + 1, Nat.succ_pos _, fun k => ?_⟩
  have hΔ0 := R.Δ_zero_pos
  have hB2 : Bmax ≤ R.Δ 0 * (P.τ:ℝ)^N := by
    rw [div_lt_iff₀ hΔ0, mul_comm] at hN
    exact hN.le
  calc R.Δ k ≤ Bmax := hbound k
    _ ≤ R.Δ 0 * (P.τ:ℝ)^N := hB2
    _ ≤ R.Δ 0 * (P.τ:ℝ)^(N+1) := by
        gcongr
        · exact hτ1.le
        · omega
