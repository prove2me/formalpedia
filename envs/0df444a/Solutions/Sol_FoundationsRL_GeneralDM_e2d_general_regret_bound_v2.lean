-- Prove2me | solution 1 for FoundationsRL.GeneralDM.e2d_general_regret_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:57:13.571601+00:00
-- url     : https://prove2.me/submissions/d0d2c7c2-33e6-4ad3-9d1e-5b11a5d7b503

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC

set_option autoImplicit false

theorem e2d_v2_sInf_le_of_forall {s : Set ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ s, x ≤ c) :
    sInf s ≤ c := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simpa using hc
  · by_cases hb : BddBelow s
    · exact (csInf_le hb hx).trans (h x hx)
    · rw [Real.sInf_of_not_bddBelow hb]; exact hc

open FoundationsRL.GeneralDM in
theorem solution {S Y : Type*} [Fintype S] [Fintype Y]
    (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S)
    (hpiStar : ∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m))
    (h𝓜 : ∀ m ∈ 𝓜, ∀ π, (∀ y, 0 ≤ m π y) ∧ ∑ y, m π y = 1)
    (γ : ℝ) (hγ : 0 < γ)
    (mstar : S → Y → ℝ) (hmstar : mstar ∈ 𝓜)
    (T : ℕ) (p : Fin T → S → ℝ) (hp : ∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1)
    (mhat : Fin T → S → Y → ℝ)
    (hmhat : ∀ t, ∀ π, (∀ y, 0 ≤ mhat t π y) ∧ ∑ y, mhat t π y = 1)
    (hatM : Set (S → Y → ℝ)) (hhatM : ∀ t, mhat t ∈ hatM)
    (hE2D : ∀ t, ∀ m ∈ 𝓜, ∑ π, p t π *
        (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mhat t π)) ≤
      decGf 𝓜 rew piStar γ (mhat t)) :
    regret (fM rew mstar) (piStar mstar) T p ≤
      (sSup ((decGf 𝓜 rew piStar γ) '' hatM)) * T +
      γ * ∑ t : Fin T, ∑ π, p t π * hellingerSq (mstar π) (mhat t π) := by
  classical
  set B : ℝ := ∑ y, |rew y| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun y _ => abs_nonneg _)
  have hfM : ∀ m ∈ 𝓜, ∀ π, |fM rew m π| ≤ B := by
    intro m hm π
    obtain ⟨h0, h1⟩ := h𝓜 m hm π
    unfold fM
    calc |∑ y, m π y * rew y| ≤ ∑ y, |m π y * rew y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |rew y| := by
        apply Finset.sum_le_sum; intro y _
        rw [abs_mul, abs_of_nonneg (h0 y)]
        have : m π y ≤ 1 := by
          rw [← h1]; exact Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ y)
        exact mul_le_of_le_one_left (abs_nonneg _) this
  have hH : ∀ P Q : Y → ℝ, 0 ≤ hellingerSq P Q :=
    fun P Q => Finset.sum_nonneg (fun y _ => sq_nonneg _)
  have hdec : ∀ mh, decGf 𝓜 rew piStar γ mh ≤ 2 * B := by
    intro mh
    unfold decGf
    apply e2d_v2_sInf_le_of_forall (by linarith)
    rintro x ⟨q, ⟨hq0, hq1⟩, rfl⟩
    apply csSup_le (Set.Nonempty.image _ ⟨mstar, hmstar⟩)
    rintro z ⟨m, hm, rfl⟩
    calc ∑ π, q π * (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mh π))
        ≤ ∑ π, q π * (2 * B) := by
          apply Finset.sum_le_sum; intro π _
          apply mul_le_mul_of_nonneg_left _ (hq0 π)
          have h1 := hfM m hm (piStar m)
          have h2 := hfM m hm π
          have h3 := mul_nonneg hγ.le (hH (m π) (mh π))
          rw [abs_le] at h1 h2
          linarith
      _ = 2 * B := by rw [← Finset.sum_mul, hq1, one_mul]
  have hbdd : BddAbove ((decGf 𝓜 rew piStar γ) '' hatM) :=
    ⟨2 * B, by rintro x ⟨mh, _, rfl⟩; exact hdec mh⟩
  have hle : ∀ t, decGf 𝓜 rew piStar γ (mhat t) ≤ sSup ((decGf 𝓜 rew piStar γ) '' hatM) :=
    fun t => le_csSup hbdd ⟨mhat t, hhatM t, rfl⟩
  have hstep : ∀ t, (fM rew mstar (piStar mstar) - ∑ π, p t π * fM rew mstar π) ≤
      sSup ((decGf 𝓜 rew piStar γ) '' hatM) +
        γ * ∑ π, p t π * hellingerSq (mstar π) (mhat t π) := by
    intro t
    have h := hE2D t mstar hmstar
    have hc : ∑ π, p t π * fM rew mstar (piStar mstar) = fM rew mstar (piStar mstar) := by
      rw [← Finset.sum_mul, (hp t).2, one_mul]
    have e : ∑ π, p t π * (fM rew mstar (piStar mstar) - fM rew mstar π -
        γ * hellingerSq (mstar π) (mhat t π)) =
        fM rew mstar (piStar mstar) - ∑ π, p t π * fM rew mstar π -
          γ * ∑ π, p t π * hellingerSq (mstar π) (mhat t π) := by
      calc ∑ π, p t π * (fM rew mstar (piStar mstar) - fM rew mstar π -
            γ * hellingerSq (mstar π) (mhat t π))
          = ∑ π, p t π * fM rew mstar (piStar mstar) - ∑ π, p t π * fM rew mstar π -
              ∑ π, γ * (p t π * hellingerSq (mstar π) (mhat t π)) := by
            rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intros; ring
        _ = _ := by rw [hc, Finset.mul_sum]
    rw [e] at h
    linarith [hle t]
  unfold regret
  calc ∑ t : Fin T, (fM rew mstar (piStar mstar) - ∑ π, p t π * fM rew mstar π)
      ≤ ∑ t : Fin T, (sSup ((decGf 𝓜 rew piStar γ) '' hatM) +
          γ * ∑ π, p t π * hellingerSq (mstar π) (mhat t π)) :=
        Finset.sum_le_sum (fun t _ => hstep t)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum]
      ring
