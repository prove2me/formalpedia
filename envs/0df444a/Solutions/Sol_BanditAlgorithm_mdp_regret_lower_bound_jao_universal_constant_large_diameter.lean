-- Prove2me | solution 1 for BanditAlgorithm.mdp_regret_lower_bound_jao_universal_constant_large_diameter
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T17:03:31.184352+00:00
-- url     : https://prove2.me/submissions/e77afa34-f331-4a39-9bbd-142320b1dbe1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BanditAlgorithm_jao_collapsed_two_state_bandit_core
import Theorems.Thm_BanditAlgorithm_jao_composite_dominates_collapsed

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A T : ℕ, ∀ D : ℝ, 10 ≤ S → 10 ≤ A →
        20 * (Real.log S / Real.log A) ≤ D → D * S * A ≤ (T : ℝ) → 12 ≤ D →
          ∀ π : MDPPolicy S A,
            ∃ M : FiniteMDP S A,
              mdpDiameterENN M ≤ ENNReal.ofReal D ∧
              ∀ s : Fin S,
                C * Real.sqrt (D * S * A * T) ≤
                  ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac s) π T) := by
  obtain ⟨c, hc, hcore⟩ := BanditAlgorithm.jao_collapsed_two_state_bandit_core
  have h22 : (0 : ℝ) < Real.sqrt 22 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨c / Real.sqrt 22, div_pos hc h22, ?_⟩
  intro S A T D hS hA hD hT hD12 π
  set m : ℕ := S / 2 * ((A - 1) / 2) with hm
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (by norm_num) hD12
  set δ : ℝ := 4 / D with hδ
  have hδ0 : 0 < δ := div_pos (by norm_num) hD0
  have hδ3 : δ ≤ 1 / 3 := by
    rw [hδ, div_le_iff₀ hD0]; linarith
  -- `m = ⌊S/2⌋·⌊(A-1)/2⌋ ≥ 20`, JAO's `kA' ≥ 20`
  have hm20 : 20 ≤ m := by
    have h1 : 5 ≤ S / 2 := by omega
    have h2 : 4 ≤ (A - 1) / 2 := by omega
    calc (20 : ℕ) = 5 * 4 := by norm_num
      _ ≤ (S / 2) * ((A - 1) / 2) := Nat.mul_le_mul h1 h2
  -- `2SA ≤ 11m`: the tight conversion `√(D'mT) ≥ √(DSAT)/√22`, equality at (S,A) = (11,10)
  have hratio : 2 * (S * A) ≤ 11 * m := by
    have h1 : 5 * S ≤ 11 * (S / 2) := by omega
    have h2 : 2 * A ≤ 5 * ((A - 1) / 2) := by omega
    have h5 : 5 * (2 * (S * A)) ≤ 5 * (11 * m) := by
      calc 5 * (2 * (S * A)) = (5 * S) * (2 * A) := by ring
        _ ≤ (11 * (S / 2)) * (5 * ((A - 1) / 2)) := Nat.mul_le_mul h1 h2
        _ = 5 * (11 * m) := by rw [hm]; ring
    exact Nat.le_of_mul_le_mul_left h5 (by norm_num)
  -- `4m ≤ SA`: the composite MDP fits in `S` states and `A` actions
  have hmSA : 4 * m ≤ S * A := by
    have h1 : 2 * (S / 2) ≤ S := by omega
    have h2 : 2 * ((A - 1) / 2) ≤ A := by omega
    calc 4 * m = (2 * (S / 2)) * (2 * ((A - 1) / 2)) := by rw [hm]; ring
      _ ≤ S * A := Nat.mul_le_mul h1 h2
  -- the core's horizon hypothesis `16m ≤ δT` is exactly `4mD ≤ T`, from `T ≥ DSA`
  have hT16 : (16 : ℝ) * m ≤ δ * T := by
    have hcast : (4 * m : ℝ) ≤ (S : ℝ) * A := by exact_mod_cast hmSA
    have h4mD : 4 * (m : ℝ) * D ≤ (T : ℝ) := by
      linarith [mul_le_mul_of_nonneg_right hcast hD0.le]
    rw [hδ, div_mul_eq_mul_div, le_div_iff₀ hD0]
    linarith
  obtain ⟨π', hdom⟩ :=
    BanditAlgorithm.jao_composite_dominates_collapsed S A D hS hA hD hD12 T π
  obtain ⟨a, ε, M', hε0, hεδ, hr0, hr1, hP1, hP0, hbound⟩ :=
    hcore m hm20 δ hδ0 hδ3 T hT16 π'
  obtain ⟨M, hdiam, hdomineq⟩ := hdom a ε M' hε0 hεδ hr0 hr1 hP1 hP0
  refine ⟨M, hdiam, fun s ↦ le_trans ?_ (le_trans hbound (hdomineq s))⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ h22]
  have hTm : (0 : ℝ) ≤ (T : ℝ) * m / δ :=
    div_nonneg (by positivity) hδ0.le
  have key : D * S * A * T ≤ ((T : ℝ) * m / δ) * 22 := by
    rw [hδ, div_div_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    have hr : (2 : ℝ) * ((S : ℝ) * A) ≤ 11 * m := by exact_mod_cast hratio
    have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    nlinarith [mul_le_mul_of_nonneg_right hr (mul_nonneg hT0 hD0.le)]
  calc c * Real.sqrt (D * S * A * T)
      ≤ c * Real.sqrt (((T : ℝ) * m / δ) * 22) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt key) hc.le
    _ = c * Real.sqrt ((T : ℝ) * m / δ) * Real.sqrt 22 := by
        rw [Real.sqrt_mul hTm]; ring
