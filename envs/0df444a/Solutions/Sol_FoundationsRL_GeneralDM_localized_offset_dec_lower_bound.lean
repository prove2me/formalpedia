-- Prove2me | solution 1 for FoundationsRL.GeneralDM.localized_offset_dec_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:57:18.241484+00:00
-- url     : https://prove2.me/submissions/c9f04c87-2d79-49c8-b3cf-8c2f59e1564b

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_FoundationsRL_GeneralDM_LocalizedSubclass

set_option autoImplicit false

open FoundationsRL.GeneralDM in
lemma p3687_regret_nonneg {S : Type*} [Fintype S] (f : S → ℝ) (ps : S)
    (hmax : ∀ π, f π ≤ f ps) (T : ℕ) (p : Fin T → S → ℝ)
    (hp : ∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1) : 0 ≤ regret f ps T p := by
  unfold regret
  apply Finset.sum_nonneg
  intro t _
  have h1 : ∑ π, p t π * f π ≤ ∑ π, p t π * f ps :=
    Finset.sum_le_sum fun π _ => mul_le_mul_of_nonneg_left (hmax π) ((hp t).1 π)
  rw [← Finset.sum_mul, (hp t).2, one_mul] at h1
  linarith

open FoundationsRL.GeneralDM in
lemma p3687_avg_mem {S : Type*} [Fintype S] (T : ℕ) (hT : 0 < T) (p : Fin T → S → ℝ)
    (hp : ∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1) :
    (fun π => (∑ t, p t π) / (T : ℝ)) ∈ {q : S → ℝ | (∀ π, 0 ≤ q π) ∧ ∑ π, q π = 1} := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  refine ⟨fun π => div_nonneg (Finset.sum_nonneg fun t _ => (hp t).1 π) hTpos.le, ?_⟩
  show ∑ π, (∑ t, p t π) / (T : ℝ) = 1
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [fun t => (hp t).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact div_self hTpos.ne'

open FoundationsRL.GeneralDM in
lemma p3687_avg_le {S : Type*} [Fintype S] (f : S → ℝ) (a : ℝ) (H : S → ℝ)
    (hH : ∀ π, 0 ≤ H π) (γ : ℝ) (hγ : 0 ≤ γ) (T : ℕ) (hT : 0 < T) (p : Fin T → S → ℝ)
    (hp : ∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1) :
    ∑ π, (∑ t, p t π) / (T : ℝ) * (a - f π - γ * H π) ≤
      (∑ t : Fin T, (a - ∑ π, p t π * f π)) / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hq : ∀ π, 0 ≤ (∑ t, p t π) / (T : ℝ) :=
    fun π => div_nonneg (Finset.sum_nonneg fun t _ => (hp t).1 π) hTpos.le
  calc ∑ π, (∑ t, p t π) / (T : ℝ) * (a - f π - γ * H π)
      ≤ ∑ π, (∑ t, p t π) / (T : ℝ) * (a - f π) :=
        Finset.sum_le_sum fun π _ =>
          mul_le_mul_of_nonneg_left (by nlinarith [hH π, mul_nonneg hγ (hH π)]) (hq π)
    _ = (∑ t : Fin T, (a - ∑ π, p t π * f π)) / T := by
        have e1 : ∀ t : Fin T, a - ∑ π, p t π * f π = ∑ π, p t π * (a - f π) := by
          intro t
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hp t).2, one_mul]
        simp_rw [e1]
        rw [Finset.sum_comm, Finset.sum_div]
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [div_mul_eq_mul_div, Finset.sum_mul]

open FoundationsRL.GeneralDM in
theorem solution :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ)
        (piStar : (S → Y → ℝ) → S), (∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m)) →
        𝓜.Nonempty →
        ∀ (T : ℕ), 0 < T →
        ∀ (p : Fin T → S → ℝ), (∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1) →
        ∃ m ∈ 𝓜, C *
          (sSup ((fun γ : ℝ =>
              sSup ((fun mhat : S → Y → ℝ =>
                  dec (localizedSubclass 𝓜 rew piStar mhat (c * γ / T)) rew piStar γ) ''
                convexHull ℝ 𝓜))
            '' {γ : ℝ | c * Real.sqrt T ≤ γ})) * T ≤
          regret (fM rew m) (piStar m) T p := by
  refine ⟨1, 1 / 2, one_pos, by norm_num, ?_⟩
  intro S Y _ _ 𝓜 rew piStar hmax hne T hT p hp
  set Φ := sSup ((fun γ : ℝ =>
              sSup ((fun mhat : S → Y → ℝ =>
                  dec (localizedSubclass 𝓜 rew piStar mhat (1 * γ / T)) rew piStar γ) ''
                convexHull ℝ 𝓜))
            '' {γ : ℝ | 1 * Real.sqrt T ≤ γ}) with hΦ
  by_contra hcon
  push Not at hcon
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨m0, hm0⟩ := hne
  have hreg0 := p3687_regret_nonneg (fM rew m0) (piStar m0) (hmax m0) T p hp
  have hlt := hcon m0 hm0
  have hΦpos : 0 < Φ := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h hTpos.le]
  have hB : 0 ≤ Φ / 2 := by linarith
  have key : Φ ≤ Φ / 2 := by
    rw [hΦ]
    refine Real.sSup_le ?_ hB
    rintro _ ⟨γ, hγ, rfl⟩
    have hγ0 : 0 ≤ γ := le_trans (by positivity) hγ
    refine Real.sSup_le ?_ hB
    rintro _ ⟨mhat, _, rfl⟩
    show dec _ rew piStar γ ≤ Φ / 2
    unfold dec
    refine Real.sSup_le ?_ hB
    rintro _ ⟨nhat, _, rfl⟩
    unfold decGf
    by_cases hbdd : BddBelow ((fun q : S → ℝ =>
      sSup ((fun m : S → Y → ℝ =>
          ∑ π, q π * (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (nhat π))) ''
          localizedSubclass 𝓜 rew piStar mhat (1 * γ / T)))
        '' {q : S → ℝ | (∀ π, 0 ≤ q π) ∧ ∑ π, q π = 1})
    · refine le_trans (csInf_le hbdd ⟨_, p3687_avg_mem T hT p hp, rfl⟩) ?_
      refine Real.sSup_le ?_ hB
      rintro _ ⟨m, hm, rfl⟩
      have hmM : m ∈ 𝓜 := hm.1
      have hH : ∀ π, 0 ≤ hellingerSq (m π) (nhat π) := fun π =>
        Finset.sum_nonneg fun y _ => sq_nonneg _
      refine le_trans (p3687_avg_le (fM rew m) (fM rew m (piStar m))
        (fun π => hellingerSq (m π) (nhat π)) hH γ hγ0 T hT p hp) ?_
      have hm := hcon m hmM
      unfold regret at hm
      rw [div_le_iff₀ hTpos]
      linarith
    · rw [Real.sInf_of_not_bddBelow hbdd]
      exact hB
  linarith
