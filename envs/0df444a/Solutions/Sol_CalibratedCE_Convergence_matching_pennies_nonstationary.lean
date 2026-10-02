-- Prove2me | solution 1 for CalibratedCE.Convergence.matching_pennies_nonstationary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:48:57.729386+00:00
-- url     : https://prove2.me/submissions/55bcafbf-3dd6-4321-9e19-969baf79a473

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_EmpDist
import Definitions.Def_CalibratedCE_Convergence_MatchingPennies

set_option autoImplicit false

namespace P366f

open CalibratedCE.Convergence CalibratedCE.Shared Filter Topology

lemma c1 : ∀ t : ℕ, ((Finset.range t).filter (fun s => mpPlay s = 1)).card = (t + 1) / 2
  | 0 => by simp
  | t + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert]
    have ih := c1 t
    by_cases h : t % 2 = 0
    · have hp : mpPlay t = 1 := by simp [mpPlay, h]
      rw [if_pos hp, Finset.card_insert_of_notMem (by simp), ih]; omega
    · have hp : ¬ mpPlay t = 1 := by simp [mpPlay, h]
      rw [if_neg hp, ih]; omega

lemma c0 : ∀ t : ℕ, ((Finset.range t).filter (fun s => mpPlay s = 0)).card = t / 2
  | 0 => by simp
  | t + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert]
    have ih := c0 t
    by_cases h : t % 2 = 0
    · have hp : ¬ mpPlay t = 0 := by simp [mpPlay, h]
      rw [if_neg hp, ih]; omega
    · have hp : mpPlay t = 0 := by simp [mpPlay, h]
      rw [if_pos hp, Finset.card_insert_of_notMem (by simp), ih]; omega

lemma half_bound (c t : ℕ) (h : 2 * c = t ∨ 2 * c = t + 1 ∨ 2 * c + 1 = t) :
    |2 * (c : ℝ) - t| ≤ 1 := by
  rcases h with h | h | h
  · have : (2 * (c : ℝ)) = t := by exact_mod_cast h
    rw [this]; simp
  · have : (2 * (c : ℝ)) = t + 1 := by exact_mod_cast h
    rw [this]; norm_num
  · have : (2 * (c : ℝ)) + 1 = t := by exact_mod_cast h
    rw [← this]; norm_num

lemma cnt (j : Fin 2) (t : ℕ) :
    |2 * (((Finset.range t).filter (fun s => mpPlay s = j)).card : ℝ) - t| ≤ 1 := by
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · rw [c0]; exact half_bound _ _ (by omega)
  · rw [c1]; exact half_bound _ _ (by omega)

lemma score_le (j : Fin 2) (t : ℕ) (ht : 1 ≤ t) :
    calibScore mpForecast mpPlay j t ≤ 1 / (t : ℝ) := by
  have hne : (Finset.range t).Nonempty := ⟨0, by simp; omega⟩
  have himg : (Finset.range t).image mpForecast = {mpForecast 0} := by
    have := Finset.image_const hne (mpForecast 0)
    exact this
  have hN : N mpForecast (mpForecast 0) t = t := by
    unfold N
    rw [Finset.filter_true_of_mem (p := fun s => mpForecast s = mpForecast 0) (fun s _ => rfl),
      Finset.card_range]
  have hfil : (Finset.range t).filter (fun s => mpForecast s = mpForecast 0 ∧ mpPlay s = j)
      = (Finset.range t).filter (fun s => mpPlay s = j) :=
    Finset.filter_congr (fun s _ => and_iff_right rfl)
  have hp : mpForecast 0 j = 1 / 2 := rfl
  unfold calibScore
  rw [himg, Finset.sum_singleton]
  unfold rho
  rw [hN, if_neg (by omega), hfil, hp]
  set c : ℝ := (((Finset.range t).filter (fun s => mpPlay s = j)).card : ℝ) with hc
  have hb := cnt j t
  rw [← hc] at hb
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [mul_div_cancel_right₀ _ htpos.ne']
  have heq : c / t - 1 / 2 = (2 * c - t) / (2 * t) := by field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * t)]
  rw [div_le_div_iff₀ (by positivity) htpos]
  nlinarith

lemma calib : Calibrated mpForecast mpPlay := by
  intro j
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_one_div_atTop_nhds_zero_nat
  · filter_upwards with t
    unfold calibScore
    apply Finset.sum_nonneg
    intro p _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with t ht
    exact score_le j t ht

lemma row_zero (s : ℕ) (a : Fin 2) : ∑ b, mpForecast s b * mpU₁ a b = 0 := by
  have : a = 0 ∨ a = 1 := by omega
  rcases this with rfl | rfl <;> simp [Fin.sum_univ_two, mpForecast, mpU₁]

lemma col_zero (s : ℕ) (b : Fin 2) : ∑ a, mpForecast s a * mpU₂ a b = 0 := by
  have : b = 0 ∨ b = 1 := by omega
  rcases this with rfl | rfl <;> simp [Fin.sum_univ_two, mpForecast, mpU₂, mpU₁]

end P366f

open CalibratedCE CalibratedCE.Convergence in
theorem solution :
    (∀ s, IsDist (mpForecast s)) ∧
    (∀ s, ∀ a' : Fin 2,
      ∑ b, mpForecast s b * mpU₁ a' b ≤ ∑ b, mpForecast s b * mpU₁ (mpPlay s) b) ∧
    (∀ s, ∀ b' : Fin 2,
      ∑ a, mpForecast s a * mpU₂ a b' ≤ ∑ a, mpForecast s a * mpU₂ a (mpPlay s)) ∧
    (¬ ∃ R : (Fin 2 → ℝ) → Fin 2, ∀ s, mpPlay s = R (mpForecast s)) ∧
    Shared.Calibrated mpForecast mpPlay ∧
    ¬ (∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, ∃ D : Fin 2 → Fin 2 → ℝ, IsCE mpU₁ mpU₂ D ∧
      ∀ a b, |empDist mpPlay mpPlay t a b - D a b| ≤ ε) := by
  refine ⟨?_, ?_, ?_, ?_, P366f.calib, ?_⟩
  · intro s
    refine ⟨fun a => by simp [mpForecast], ?_⟩
    simp [mpForecast]
  · intro s a'
    rw [P366f.row_zero, P366f.row_zero]
  · intro s b'
    rw [P366f.col_zero, P366f.col_zero]
  · rintro ⟨R, hR⟩
    have h0 := hR 0
    have h1 := hR 1
    have : mpForecast 0 = mpForecast 1 := rfl
    rw [this, ← h1] at h0
    exact absurd h0 (by decide)
  · intro h
    obtain ⟨T, hT⟩ := h (1 / 8) (by norm_num)
    obtain ⟨D, hD, hclose⟩ := hT T le_rfl
    obtain ⟨⟨_, hsum⟩, _, h2⟩ := hD
    have e01 : empDist mpPlay mpPlay T 0 1 = 0 := by
      unfold empDist
      rw [Finset.filter_false_of_mem (fun s _ hs => by
        obtain ⟨ha, hb⟩ := hs
        rw [ha] at hb
        exact absurd hb (by decide))]
      simp
    have e10 : empDist mpPlay mpPlay T 1 0 = 0 := by
      unfold empDist
      rw [Finset.filter_false_of_mem (fun s _ hs => by
        obtain ⟨ha, hb⟩ := hs
        rw [ha] at hb
        exact absurd hb (by decide))]
      simp
    have hc01 := hclose 0 1
    have hc10 := hclose 1 0
    rw [e01] at hc01
    rw [e10] at hc10
    have hsw := h2 (fun b => if b = 0 then 1 else 0)
    simp [Fin.sum_univ_two, mpU₂, mpU₁] at hsw hsum
    rw [abs_le] at hc01 hc10
    linarith [hc01.1, hc10.1]
