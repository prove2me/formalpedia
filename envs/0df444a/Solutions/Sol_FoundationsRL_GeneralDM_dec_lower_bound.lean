-- Prove2me | solution 1 for FoundationsRL.GeneralDM.dec_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:48:57.661311+00:00
-- url     : https://prove2.me/submissions/adb8dbc8-e782-4554-a217-143a39d19709

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_ConstrainedDEC

set_option autoImplicit false

open FoundationsRL.GeneralDM in
theorem d1769626_fM_comb {S Y : Type*} [Fintype S] [Fintype Y] (rew : Y → ℝ)
    (x z : S → Y → ℝ) (a b : ℝ) (π : S) :
    fM rew (a • x + b • z) π = a * fM rew x π + b * fM rew z π := by
  simp only [fM, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

open FoundationsRL.GeneralDM in
theorem d1769626_key {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ))
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S)
    (hopt : ∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m)) (ε : ℝ)
    (q : S → ℝ) (hq : (∀ π, 0 ≤ q π) ∧ ∑ π, q π = 1) (B : ℝ) (hB : 0 ≤ B)
    (hM : ∀ m ∈ 𝓜, ∑ π, q π * (fM rew m (piStar m) - fM rew m π) ≤ B) :
    decC 𝓜 rew piStar ε ≤ B := by
  set K : Set (S → Y → ℝ) := {m | ∀ π', ∑ π, q π * (fM rew m π' - fM rew m π) ≤ B} with hK
  have hKc : Convex ℝ K := by
    intro x hx z hz a b ha hb hab π'
    have h1 : ∑ π, q π * (fM rew x π' - fM rew x π) ≤ B := hx π'
    have h2 : ∑ π, q π * (fM rew z π' - fM rew z π) ≤ B := hz π'
    have e : ∑ π, q π * (fM rew (a • x + b • z) π' - fM rew (a • x + b • z) π)
        = a * ∑ π, q π * (fM rew x π' - fM rew x π)
          + b * ∑ π, q π * (fM rew z π' - fM rew z π) := by
      simp only [d1769626_fM_comb, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun π _ => by ring)
    show ∑ π, q π * (fM rew (a • x + b • z) π' - fM rew (a • x + b • z) π) ≤ B
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  have hMK : 𝓜 ⊆ K := by
    intro m hm π'
    refine le_trans (Finset.sum_le_sum (fun π _ => ?_)) (hM m hm)
    exact mul_le_mul_of_nonneg_left (by linarith [hopt m π']) (hq.1 π)
  have hHull : convexHull ℝ 𝓜 ⊆ K := convexHull_min hMK hKc
  unfold decC
  apply Real.sSup_le _ hB
  rintro _ ⟨mhat, hmhat, rfl⟩
  beta_reduce
  unfold decCGf
  by_cases hbdd : BddBelow ((fun p : S → ℝ =>
      sSup ((fun m : S → Y → ℝ => ∑ π, p π * (fM rew m (piStar m) - fM rew m π)) ''
        {m ∈ insert mhat 𝓜 | ∑ π, p π * hellingerSq (m π) (mhat π) ≤ ε ^ 2}))
    '' {p : S → ℝ | (∀ π, 0 ≤ p π) ∧ ∑ π, p π = 1})
  · refine le_trans (csInf_le hbdd ⟨q, hq, rfl⟩) ?_
    apply Real.sSup_le _ hB
    rintro _ ⟨m, ⟨hm, _⟩, rfl⟩
    rcases (Set.mem_insert_iff.mp hm) with h | h
    · rw [h]
      exact hHull hmhat (piStar mhat)
    · exact hM m h
  · rw [Real.sInf_of_not_bddBelow hbdd]
    exact hB

open FoundationsRL.GeneralDM in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧
      ∀ {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ)
      (piStar : (S → Y → ℝ) → S), (∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m)) →
      ∀ T : ℕ, 0 < T →
      decC 𝓜 rew piStar (c / Real.sqrt T) ≥ 10 * (c / Real.sqrt T) →
      ∀ p : Fin T → S → ℝ, (∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1) →
      ∃ m ∈ 𝓜, c' * decC 𝓜 rew piStar (c / Real.sqrt T) * T ≤
        regret (fM rew m) (piStar m) T p := by
  refine ⟨1, one_pos, 1 / 2, by norm_num, ?_⟩
  intro S Y _ _ 𝓜 rew piStar hopt T hT hloc p hp
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hε : 0 < 1 / Real.sqrt T := by positivity
  set D := decC 𝓜 rew piStar (1 / Real.sqrt T) with hD
  have hDpos : 0 < D := by linarith
  by_contra hcon
  push Not at hcon
  set q : S → ℝ := fun π => (∑ t, p t π) / T with hqdef
  have hq : (∀ π, 0 ≤ q π) ∧ ∑ π, q π = 1 := by
    refine ⟨fun π => div_nonneg (Finset.sum_nonneg (fun t _ => (hp t).1 π)) hTpos.le, ?_⟩
    simp only [hqdef]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp only [fun t => (hp t).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    field_simp
  have hreg : ∀ m, regret (fM rew m) (piStar m) T p
      = T * ∑ π, q π * (fM rew m (piStar m) - fM rew m π) := by
    intro m
    unfold regret
    have e : ∀ t : Fin T, fM rew m (piStar m) - ∑ π, p t π * fM rew m π
        = ∑ π, p t π * (fM rew m (piStar m) - fM rew m π) := by
      intro t
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hp t).2, one_mul]
    rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun π _ => ?_)
    simp only [hqdef]
    rw [← Finset.sum_mul]
    field_simp
  have hM : ∀ m ∈ 𝓜, ∑ π, q π * (fM rew m (piStar m) - fM rew m π) ≤ D / 2 := by
    intro m hm
    have h := hcon m hm
    rw [hreg] at h
    nlinarith
  have := d1769626_key 𝓜 rew piStar hopt (1 / Real.sqrt T) q hq (D / 2) (by linarith) hM
  linarith

