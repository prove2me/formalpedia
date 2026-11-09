-- Prove2me | solution 1 for FamilyGenTest.threshold_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:52:22.469341+00:00
-- url     : https://prove2.me/submissions/2d96b94e-2613-49b0-a2cd-f710b44cee56

import Mathlib
import Definitions.Def_FamilyGenTest_Pmax

namespace Aux_FamilyGenTest_thr

open FamilyGenTest

theorem quad_pos (A B C p : ℝ) (hA : 0 < A) :
    0 ≤ -A * p ^ 2 + B * p - C ↔ 4 * (A * C) ≤ B ^ 2 ∧
      (B - Real.sqrt (B ^ 2 - 4 * (A * C))) / (2 * A) ≤ p ∧
      p ≤ (B + Real.sqrt (B ^ 2 - 4 * (A * C))) / (2 * A) := by
  have h2A : 0 < 2 * A := by linarith
  constructor
  · intro h
    have hsq : (2 * A * p - B) ^ 2 ≤ B ^ 2 - 4 * (A * C) := by nlinarith [mul_nonneg hA.le h]
    have hD : 0 ≤ B ^ 2 - 4 * (A * C) := le_trans (sq_nonneg _) hsq
    have habs := Real.abs_le_sqrt hsq
    rw [abs_le] at habs
    refine ⟨by linarith, ?_, ?_⟩
    · rw [div_le_iff₀ h2A]; linarith
    · rw [le_div_iff₀ h2A]; linarith
  · rintro ⟨hD, h1, h2⟩
    rw [div_le_iff₀ h2A] at h1
    rw [le_div_iff₀ h2A] at h2
    have hs := Real.sq_sqrt (show 0 ≤ B ^ 2 - 4 * (A * C) by linarith)
    have habs : |2 * A * p - B| ≤ Real.sqrt (B ^ 2 - 4 * (A * C)) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hsq : (2 * A * p - B) ^ 2 ≤ B ^ 2 - 4 * (A * C) := by
      calc (2 * A * p - B) ^ 2 = |2 * A * p - B| ^ 2 := (sq_abs _).symm
        _ ≤ (Real.sqrt (B ^ 2 - 4 * (A * C))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = _ := hs
    have h4 : 0 ≤ (4 * A) * (-A * p ^ 2 + B * p - C) := by nlinarith
    exact (mul_nonneg_iff_of_pos_left (by linarith : (0:ℝ) < 4 * A)).mp h4

theorem quad_part (A B C : ℝ) (hA : 0 ≤ A) :
      (QuadExists A B C → quadMin A B C ≤ quadMax A B C) ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
        (0 ≤ -A * p ^ 2 + B * p - C ↔
          QuadExists A B C ∧ quadMin A B C ≤ p ∧ p ≤ quadMax A B C) := by
  rcases hA.eq_or_lt with rfl | hA
  · unfold QuadExists quadMin quadMax
    rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    rcases lt_trichotomy B 0 with hB | rfl | hB
    · rw [if_neg (not_lt.mpr hB.le), if_pos hB, if_neg (not_lt.mpr hB.le), if_pos hB]
      refine ⟨fun _ => min_le_left _ _, fun p hp0 hp1 => ?_⟩
      constructor
      · intro h
        refine ⟨fun hb => absurd hb hB.ne, min_le_of_right_le hp0, ?_⟩
        rw [le_div_iff_of_neg hB]; linarith
      · rintro ⟨-, -, h2⟩
        rw [le_div_iff_of_neg hB] at h2; linarith
    · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
      refine ⟨fun _ => zero_le_one, fun p hp0 hp1 => ?_⟩
      constructor
      · intro h
        exact ⟨fun _ => by linarith, hp0, hp1⟩
      · rintro ⟨h, -, -⟩
        have := h rfl
        linarith
    · rw [if_pos hB, if_pos hB]
      refine ⟨fun _ => le_max_left _ _, fun p hp0 hp1 => ?_⟩
      constructor
      · intro h
        refine ⟨fun hb => absurd hb hB.ne', ?_, le_max_of_le_right hp1⟩
        rw [div_le_iff₀ hB]; linarith
      · rintro ⟨-, h1, -⟩
        rw [div_le_iff₀ hB] at h1; linarith
  · unfold QuadExists quadMin quadMax
    rw [if_pos hA, if_pos hA, if_pos hA]
    refine ⟨fun hD => ?_, fun p _ _ => quad_pos A B C p hA⟩
    have h2A : 0 < 2 * A := by linarith
    have := Real.sqrt_nonneg (B ^ 2 - 4 * (A * C))
    exact div_le_div_of_nonneg_right (by linarith) h2A.le

end Aux_FamilyGenTest_thr

open FamilyGenTest in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] :
    (∀ A B C : ℝ, 0 ≤ A →
      (QuadExists A B C → quadMin A B C ≤ quadMax A B C) ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
        (0 ≤ -A * p ^ 2 + B * p - C ↔
          QuadExists A B C ∧ quadMin A B C ≤ p ∧ p ≤ quadMax A B C)) ∧
    ∀ (R : Rewards I) (μ : Prior I) (s : State I) (i : I), CensoredOrder R →
      (ThresholdsExist R μ s i → Pmin R μ s i ≤ Pmax R μ s i) ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
        (0 ≤ gap R μ s i p ↔
          ThresholdsExist R μ s i ∧ Pmin R μ s i ≤ p ∧ p ≤ Pmax R μ s i) := by
  refine ⟨fun A B C hA => Aux_FamilyGenTest_thr.quad_part A B C hA, ?_⟩
  intro R μ s i hR
  have hr : 0 ≤ rdelta R i := by
    unfold rdelta
    have := hR i
    linarith [this.1, this.2]
  exact Aux_FamilyGenTest_thr.quad_part _ _ _ hr
